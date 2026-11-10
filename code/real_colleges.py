# -*- coding: utf-8 -*-
"""Real-data analysis of the colleges of mayors that would elect the condes in Santa Catarina.
Counties = the 17 SUS health regions (Deliberacao 38/CIB/2024); electors = mayors elected in 2024.
Outputs ../out/real_colleges.json and printed tables."""
import json, itertools, numpy as np, pandas as pd
m = pd.read_csv("../data/sc_master.csv")
P = m.pop2022.sum()
CENTRAO5 = ["MDB","PP","PSD","UNIÃO","REPUBLICANOS"]
BLOCS = {"PL":"Right (PL, NOVO)","NOVO":"Right (PL, NOVO)","MDB":"Centre (MDB, PP, PSD, UNIÃO, REPUBLICANOS, PODEMOS)",
         "PP":"Centre (MDB, PP, PSD, UNIÃO, REPUBLICANOS, PODEMOS)","PSD":"Centre (MDB, PP, PSD, UNIÃO, REPUBLICANOS, PODEMOS)",
         "UNIÃO":"Centre (MDB, PP, PSD, UNIÃO, REPUBLICANOS, PODEMOS)","REPUBLICANOS":"Centre (MDB, PP, PSD, UNIÃO, REPUBLICANOS, PODEMOS)",
         "PODEMOS":"Centre (MDB, PP, PSD, UNIÃO, REPUBLICANOS, PODEMOS)","PSDB":"PSDB-Cidadania","CIDADANIA":"PSDB-Cidadania","PT":"Left (PT)"}
m["bloc"] = m.party_2024.map(BLOCS)

def plurality(df, col, weight=None):
    w = df[weight] if weight else pd.Series(1.0, index=df.index)
    s = w.groupby(df[col]).sum().sort_values(ascending=False)
    top = s.index[0]; tie = len(s)>1 and np.isclose(s.iloc[0], s.iloc[1])
    return top, s.iloc[0]/s.sum(), tie, (s.iloc[0]/s.sum() > 0.5)

rows=[]
for r, df in m.groupby("health_region_2024"):
    p1, sh1, t1, maj1 = plurality(df,"party_2024")
    p2, sh2, t2, maj2 = plurality(df,"party_2024","pop2022")
    b1, bs1, bt1, bm1 = plurality(df,"bloc")
    polo = df.loc[df.pop2022.idxmax()]
    rows.append(dict(region=r, n=len(df), pop=int(df.pop2022.sum()), polo=polo.municipality, polo_party=polo.party_2024,
        polo_pop_share=polo.pop2022/df.pop2022.sum(),
        plur_1m1v=p1, share_1m1v=sh1, tie_1m1v=t1, abs_maj_1m1v=maj1,
        plur_pop=p2, share_pop=sh2, tie_pop=t2, abs_maj_pop=maj2,
        bloc_1m1v=b1, bloc_share=bs1, bloc_tie=bt1,
        centrao5_share_mayors=df.party_2024.isin(CENTRAO5).mean(),
        pl_share_mayors=(df.party_2024=="PL").mean()))
R = pd.DataFrame(rows).sort_values("pop", ascending=False)
pd.set_option("display.width",250)
print(R[["region","n","polo","polo_party","polo_pop_share","plur_1m1v","share_1m1v","tie_1m1v","plur_pop","share_pop","bloc_1m1v","bloc_share"]].to_string(index=False))

# party shares: mayors, population governed, condes under each rule
mayors = m.party_2024.value_counts()/len(m)
popgov = m.groupby("party_2024").pop2022.sum()/P
def conde_share(col, tiecol):
    s = {}
    for _,r in R.iterrows():
        s[r[col]] = s.get(r[col],0) + (0.5 if r[tiecol] else 1.0)   # ties split (resolved below explicitly)
    return pd.Series(s)/len(R)
c1 = R.plur_1m1v.value_counts()/len(R); c2 = R.plur_pop.value_counts()/len(R)
tab = pd.DataFrame({"mayors":mayors,"pop_governed":popgov,"condes_1m1v":c1,"condes_popweighted":c2}).fillna(0).sort_values("mayors",ascending=False)
print("\nParty shares (ties counted for the first-listed party; see tie flags):"); print((100*tab).round(1).to_string())
print("ties 1m1v:", R[R.tie_1m1v][["region","plur_1m1v"]].values.tolist(), " ties pop:", R[R.tie_pop][["region"]].values.tolist())

# exact tie handling: list parties tied at the top in each region (1m1v)
ties = {}
for r, df in m.groupby("health_region_2024"):
    s = df.party_2024.value_counts(); top = s[s==s.iloc[0]].index.tolist()
    ties[r] = top
print("\nTop parties per region (1m1v, all tied listed):"); [print(f"  {k}: {v} ({df_n})") for k,v,df_n in [(k,v,len(m[m.health_region_2024==k])) for k,v in ties.items()]]

# ---------------- Banzhaf power of each municipality (exact, dynamic programming) -------------
def banzhaf_single(w, quota_frac=0.5):
    """w: integer weights. Coalition wins if weight > quota_frac*sum(w). Returns normalized Banzhaf and absolute (swing prob)."""
    w = np.asarray(w, dtype=np.int64); n=len(w); W=int(w.sum()); q=quota_frac*W
    swings = np.zeros(n)
    for i in range(n):
        cnt = np.zeros(W+1, dtype=np.float64); cnt[0]=1.0
        for j in range(n):
            if j==i: continue
            cnt[w[j]:] = cnt[w[j]:] + cnt[:W+1-w[j]].copy()
        tot = np.arange(W+1)
        swings[i] = cnt[(tot<=q) & (tot+w[i]>q)].sum()
    return swings/swings.sum(), swings/2**(n-1)

def banzhaf_dual(pop, unit=10):
    """Dual majority: coalition wins iff > half of members AND > half of population."""
    p = np.maximum(1, np.round(np.asarray(pop)/unit)).astype(np.int64); n=len(p); W=int(p.sum())
    swings=np.zeros(n)
    for i in range(n):
        cnt = np.zeros((n, W+1)); cnt[0,0]=1.0          # cnt[k, w] = #subsets of others with k members, weight w
        for j in range(n):
            if j==i: continue
            cnt[1:, p[j]:] = cnt[1:, p[j]:] + cnt[:-1, :W+1-p[j]].copy()
        k = np.arange(n)[:,None]; tw = np.arange(W+1)[None,:]
        win_with = ((k+1) > n/2) & ((tw+p[i]) > W/2)
        win_without = (k > n/2) & (tw > W/2)
        swings[i] = cnt[win_with & ~win_without].sum()
    return swings/swings.sum(), swings/2**(n-1)

B=[]
for r, df in m.groupby("health_region_2024"):
    df = df.sort_values("pop2022", ascending=False); n=len(df)
    nb_pop, ab_pop = banzhaf_single(df.pop2022.values)
    nb_dual, ab_dual = banzhaf_dual(df.pop2022.values)
    B.append(dict(region=r, n=n, polo=df.municipality.iloc[0], polo_pop_share=df.pop2022.iloc[0]/df.pop2022.sum(),
                  banzhaf_1m1v=1/n, banzhaf_pop=nb_pop[0], banzhaf_dual=nb_dual[0],
                  smallest_share_pop=nb_pop.min(), smallest_share_dual=nb_dual.min()))
Bz = pd.DataFrame(B).sort_values("polo_pop_share", ascending=False)
print("\nNormalized Banzhaf power of the polo city:"); print(Bz.round(3).to_string(index=False))
out = dict(regions=R.to_dict(orient="records"), party_table=(tab.reset_index().rename(columns={"index":"party"})).to_dict(orient="records"),
           banzhaf=Bz.to_dict(orient="records"), ties_1m1v=ties)
json.dump(out, open("../out/real_colleges.json","w"), ensure_ascii=False, indent=1, default=float)
