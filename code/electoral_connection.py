# -*- coding: utf-8 -*-
"""The electoral connection in Santa Catarina: where deputies' votes come from, whether their 2025 special transfers
follow their votes, and whether the transfers are associated with their votes in 2026.

Inputs  data/derived/tse_fed_2022.csv, tse_fed_2026.csv, tse_summary.json (prep_tse.py)
        data/derived/sq_alloc.npz (pix_dm: 2025 special transfers by deputy and municipality), sc_master2.csv
Outputs out/electoral_connection.json
"""
import os, json
import numpy as np, pandas as pd
import statsmodels.api as sm

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DER, OUT = os.path.join(ROOT, "data", "derived"), os.path.join(ROOT, "out")
from prep_tse import PIX_TO_TSE

m = pd.read_csv(os.path.join(DER, "sc_master2.csv"))
ids = m.ibge_id.values
M = len(ids)
pos = {i: k for k, i in enumerate(ids)}
pop = m.pop2022.values.astype(float)
a = np.load(os.path.join(DER, "sq_alloc.npz"), allow_pickle=True)
pix = a["pix_dm"]                                   # R$ planned in 2025, deputy x municipality
names = [str(x) for x in a["dep_names"]]
dparty = [str(x) for x in a["dep_party"]]
low = a["low_pix"]
v22 = pd.read_csv(os.path.join(DER, "tse_fed_2022.csv"))
v26 = pd.read_csv(os.path.join(DER, "tse_fed_2026.csv"))
S = json.load(open(os.path.join(DER, "tse_summary.json")))
info = {r["pix_name"]: r for r in S["deputies_2022"]}


def tot(v):
    t = v.groupby("ibge_id").votes_valid.sum()
    return np.array([t.get(i, 0) for i in ids], float)


T22, T26 = tot(v22), tot(v26)


def mat(v, ballot_or_key, by="ballot_name"):
    x = np.zeros(M)
    s = v[v[by] == ballot_or_key].groupby("ibge_id").votes_valid.sum()
    for i, val in s.items():
        x[pos[i]] = val
    return x


D = len(names)
V22 = np.array([mat(v22[v22.elected == 1], PIX_TO_TSE[n]) for n in names])          # 2022 votes of each deputy
name22 = {PIX_TO_TSE[n]: v22[v22.ballot_name == PIX_TO_TSE[n]].name.iloc[0] for n in names}
V26 = np.array([mat(v26, name22[PIX_TO_TSE[n]], by="name") for n in names])          # 2026 votes (0 if not running)
ran = np.array([info[n]["ran_2026"] for n in names], bool)
p26 = [info[n]["party_2026"] for n in names]
R = {}
# ------------------------------------------------------------------ 1. where the votes come from
sh = V22 / V22.sum(1, keepdims=True)
top1 = sh.max(1)
n50 = np.array([np.searchsorted(np.cumsum(np.sort(s)[::-1]), 0.5) + 1 for s in sh])
dom = np.array([(sh[d] * V22[d] / np.maximum(T22, 1)).sum() for d in range(D)])     # vote-weighted local share
R["votes_top_municipality_share_median"] = float(np.median(top1))
R["votes_top_municipality_share_range"] = [float(top1.min()), float(top1.max())]
R["municipalities_for_half_of_votes_median"] = float(np.median(n50))
R["municipalities_for_half_of_votes_range"] = [int(n50.min()), int(n50.max())]
R["dominance_median"] = float(np.median(dom))
R["population_top_municipality_share"] = float(pop.max() / pop.sum())
# ------------------------------------------------------------------ 2. do the transfers follow the votes?
hi = ~low
mon = pix / np.maximum(pix.sum(1, keepdims=True), 1)
r_dep = [float(np.corrcoef(mon[d], sh[d])[0, 1]) for d in range(D) if hi[d]]
R["corr_money_votes_by_deputy_median"] = float(np.median(r_dep))
R["corr_money_votes_by_deputy_range"] = [float(min(r_dep)), float(max(r_dep))]
# share of each deputy's money in the municipalities that supplied half of his or her votes, against their share of
# the state's population
inbase = np.zeros_like(sh, bool)
for d in range(D):
    o = np.argsort(-sh[d]);
    k = n50[d]
    inbase[d, o[:k]] = True
mb = [float(mon[d][inbase[d]].sum()) for d in range(D) if hi[d]]
pb = [float(pop[inbase[d]].sum() / pop.sum()) for d in range(D) if hi[d]]
R["money_share_in_vote_base_median"] = float(np.median(mb))
R["population_share_of_vote_base_median"] = float(np.median(pb))
# PPML of money on the deputy's local vote share, with deputy fixed effects (targeting.py, also used to impute the
# geography of the three deputies who used special transfers little)
from targeting import fit
mayor_party = m.party.values
gdp_pc = m.gdp_pc_2021.values
beta_t, se_t, glm, n_t = fit(pix, V22, T22, pop, gdp_pc, mayor_party, np.array(dparty), hi)
R["ppml"] = {k: [float(b_), float(s_)] for k, b_, s_ in zip(["lvs", "lpop", "same", "lgdp"], beta_t, se_t)}
R["ppml_n"] = n_t
R["ppml_same_party_ratio"] = float(np.exp(beta_t[2]))
R["recipients_per_deputy_median"] = float(np.median((pix[hi] > 0).sum(1)))
# in-sample fit of the imputation rule used for the three small users (prep_data2.py): predicted shares restricted to
# the K municipalities with the largest predictions, against the actual shares of the thirteen
from targeting import shares
K = int(R["recipients_per_deputy_median"])
c_k, c_f, inK = [], [], []
for d in np.where(hi)[0]:
    act = pix[d] / pix[d].sum()
    vs = V22[d] / np.maximum(T22, 1)
    pk = shares(beta_t, vs, pop, gdp_pc, mayor_party == dparty[d], K)
    pf = shares(beta_t, vs, pop, gdp_pc, mayor_party == dparty[d], None)
    c_k.append(float(np.corrcoef(act, pk)[0, 1]));
    c_f.append(float(np.corrcoef(act, pf)[0, 1]))
    inK.append(float(act[pk > 0].sum()))
R["imputation_corr_topK_median"] = float(np.median(c_k))
R["imputation_corr_full_median"] = float(np.median(c_f))
R["imputation_money_in_topK_median"] = float(np.median(inK))
reel = [names[d] for d in range(D) if info[names[d]]["elected_2026"] == 1]
R["reelected_2026"] = reel
R["n_new_2026"] = int(16 - len(reel))
# ------------------------------------------------------------------ 3. are the transfers associated with 2026 votes?
s22 = 100 * V22 / np.maximum(T22, 1)[None, :]
s26 = 100 * V26 / np.maximum(T26, 1)[None, :]
pixpc = pix / pop[None, :] / 100.0                    # R$ 100 per inhabitant
rows = []
for d in np.where(ran)[0]:
    for j in range(M):
        rows.append({"d": d, "j": j, "dy": s26[d, j] - s22[d, j], "y26": s26[d, j], "y22": s22[d, j],
                     "pixpc": pixpc[d, j], "same": float(mayor_party[j] == {"PODE": "PODEMOS"}.get(p26[d], p26[d])),
                     "switch": float(p26[d] != dparty[d]), "low": float(low[d])})
E = pd.DataFrame(rows)


def twfe(data, y, xs):
    X = pd.concat([data[xs], pd.get_dummies(data.d, prefix="d", drop_first=True).astype(float),
                   pd.get_dummies(data.j, prefix="j", drop_first=True).astype(float)], axis=1)
    X = sm.add_constant(X)
    f = sm.OLS(data[y], X).fit(cov_type="cluster", cov_kwds={"groups": data.j.values})
    return {k: [float(f.params[k]), float(f.bse[k])] for k in xs}, int(len(data))


R["return_main"], R["return_n"] = twfe(E, "y26", ["pixpc", "y22", "same"])
R["return_change"], _ = twfe(E, "dy", ["pixpc", "same"])
R["return_no_switchers"], R["return_no_switchers_n"] = twfe(E[E.switch == 0], "y26", ["pixpc", "y22", "same"])
R["return_only_users"], R["return_only_users_n"] = twfe(E[E.low == 0], "y26", ["pixpc", "y22", "same"])
# weighted by the municipality's valid votes (effect on the deputy's statewide votes) and in logs of votes
E["w"] = [T26[j] for j in E.j]
E["lv26"] = [np.log1p(V26[d, j]) for d, j in zip(E.d, E.j)]
E["lv22"] = [np.log1p(V22[d, j]) for d, j in zip(E.d, E.j)]


def twfe_w(data, y, xs, w):
    X = pd.concat([data[xs], pd.get_dummies(data.d, prefix="d", drop_first=True).astype(float),
                   pd.get_dummies(data.j, prefix="j", drop_first=True).astype(float)], axis=1)
    X = sm.add_constant(X)
    f = sm.WLS(data[y], X, weights=data[w]).fit(cov_type="cluster", cov_kwds={"groups": data.j.values})
    return {k: [float(f.params[k]), float(f.bse[k])] for k in xs}


R["return_weighted"] = twfe_w(E, "y26", ["pixpc", "y22", "same"], "w")
R["return_logvotes"], _ = twfe(E, "lv26", ["pixpc", "lv22", "same"])
# binned relation for the figure: residuals of the 2026 share and of transfers per inhabitant on the fixed effects
# and the 2022 share (Frisch-Waugh), in 20 bins of transfers among cells that received money, plus the zero cell
Xc = pd.concat([E[["y22", "same"]], pd.get_dummies(E.d, prefix="d", drop_first=True).astype(float),
                pd.get_dummies(E.j, prefix="j", drop_first=True).astype(float)], axis=1)
Xc = sm.add_constant(Xc)
ry = sm.OLS(E.y26, Xc).fit().resid
rx = sm.OLS(E.pixpc, Xc).fit().resid
q = pd.qcut(rx, 20, labels=False, duplicates="drop")
R["binned"] = [[float(rx[q == b].mean()), float(ry[q == b].mean()), int((q == b).sum())] for b in sorted(set(q))]
# implied cost of a vote: extra votes = beta/100 x (R$100 per inhabitant) x valid votes of the municipality in 2026
bb = R["return_main"]["pixpc"][0]
used = E.d.unique()
extra = sum(bb / 100 * pixpc[d, j] * T26[j] for d in used for j in range(M))
money = sum(pix[d].sum() for d in used)
R["implied_extra_votes"] = float(extra)
R["implied_money"] = float(money)
R["implied_reais_per_vote"] = float(money / extra) if extra > 0 else None
R["pixpc_mean_among_receivers"] = float(np.mean(pixpc[pix > 0] * 100))
R["share_cells_with_money"] = float((pix[hi] > 0).mean())
json.dump(R, open(os.path.join(OUT, "electoral_connection.json"), "w"), indent=1, ensure_ascii=False)
for k, v in R.items():
    print(k, v)
