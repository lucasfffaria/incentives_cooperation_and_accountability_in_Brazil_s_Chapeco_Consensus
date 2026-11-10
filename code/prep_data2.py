# -*- coding: utf-8 -*-
"""Build the municipal data set, the real status-quo allocation and the data moments used by the model.

Inputs (all read-only):
  data/sc_master.csv                      municipalities, health regions, coordinates, GDP pc, 2024 mayors (old package)
  data/companion/sc_municipalities_base.csv   companion package: fiscal, census, Pix totals, mayors
  data/companion/sc_pix2025_plans.csv     2025 special-transfer plans to SC beneficiaries (author x municipality)
  data/companion/sc_mayors_panel_2016_2024.csv, sc_incumbency_2012_2024.csv
  data/derived/tse_fed_2022.csv, tse_fed_2026.csv, tse_summary.json (prep_tse.py: TSE votes for the Chamber)
Outputs:
  data/derived/sc_master2.csv, data/derived/sq_alloc.npz, data/derived/data_stats.json
"""
import json, os
import numpy as np, pandas as pd

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
D = os.path.join(ROOT, "data")
C = os.path.join(D, "companion")
OUT = os.path.join(D, "derived")
os.makedirs(OUT, exist_ok=True)

QUOTA = 37.2e6          # individual-amendment quota per deputy, 2025 (Agencia Senado, 2025)
N_DEP = 16

m = pd.read_csv(os.path.join(D, "sc_master.csv"))
b = pd.read_csv(os.path.join(C, "sc_municipalities_base.csv")).rename(columns={"cod_ibge": "ibge_id"})
m = m.merge(b[["ibge_id", "higher_ed_share", "own_tax_share_2024", "rev_current_2024", "fpm_gross_2024",
               "rev_taxes_2024", "bf_share_households", "literacy15_census", "sh_sewer_census", "ideb_2023",
               "pop2024", "hierarquia_urbana"]], on="ibge_id", how="left", validate="one_to_one")
assert len(m) == 295
pop = m.pop2022.values.astype(float)

# ---------------------------------------------------------------- need and capacity
need = 1.0 / m.gdp_pc_2021.values
need = need / np.average(need, weights=pop)
m["need"] = need

# own-tax share and current revenue are missing for 41 municipalities (SICONFI coverage): impute by OLS on
# log population, log GDP pc and the higher-education share (fit on the 254 reporters)
X = np.column_stack([np.ones(295), np.log(pop), np.log(m.gdp_pc_2021.values), m.higher_ed_share.values,
                     np.log(m.fpm_gross_2024.values / pop)])
ok = m.own_tax_share_2024.notna().values
beta_tax, *_ = np.linalg.lstsq(X[ok], np.log(m.own_tax_share_2024.values[ok]), rcond=None)
tax_hat = np.exp(X @ beta_tax)
m["own_tax_share_imp"] = np.where(ok, m.own_tax_share_2024.values, tax_hat)
m["own_tax_imputed"] = (~ok).astype(int)
okr = m.rev_current_2024.notna().values
beta_rev, *_ = np.linalg.lstsq(X[okr], np.log(m.rev_current_2024.values[okr] / pop[okr]), rcond=None)
rev_pc_hat = np.exp(X @ beta_rev)
m["rev_pc"] = np.where(okr, m.rev_current_2024.values / pop, rev_pc_hat)
m["rev_imputed"] = (~okr).astype(int)
r2 = 1 - np.var(np.log(m.rev_current_2024.values[okr] / pop[okr]) - (X @ beta_rev)[okr]) / np.var(
    np.log(m.rev_current_2024.values[okr] / pop[okr]))


def z(v):
    v = np.asarray(v, float)
    return (v - v.mean()) / v.std()


# technical capacity index: mean of standardized log population, higher-education share and own-tax share
cap_raw = (z(np.log(pop)) + z(m.higher_ed_share.values) + z(m.own_tax_share_imp.values)) / 3
cap_z = z(cap_raw)
m["cap_z"] = cap_z
m["kappa"] = 1 / (1 + np.exp(-cap_z))          # in (0, 1); unweighted mean about 0.5

# ---------------------------------------------------------------- Pix plans, author fixes
p = pd.read_csv(os.path.join(C, "sc_pix2025_plans.csv"))
p = p[p.codigo_ibge_municipio.notna()].copy()
p["ibge_id"] = p.codigo_ibge_municipio.astype(int)
p = p[p.ibge_id.isin(m.ibge_id)]
fix = {"Caroline de Toni": ("DEPUTADO FEDERAL", "PL", "CAROL DE TONI"),
       "Ivete da Silveira": ("SENADOR", "MDB", "IVETE DA SILVEIRA")}
for k, (cargo, party, _) in fix.items():
    sel = p.nome_parlamentar_emenda_plano_acao == k
    p.loc[sel, "cargo"] = cargo
    p.loc[sel, "partido_eleicao"] = party
assert p.cargo.notna().all() and p.partido_eleicao.notna().all()
# the 16 deputies elected in 2022, with Pix author names
DEPS = [("Carmen Zanotto", "CIDADANIA"), ("Caroline de Toni", "PL"), ("Jorge Goetten", "PL"),
        ("Julia Zanatta", "PL"), ("Daniel Freitas", "PL"), ("Daniela Reinehr", "PL"), ("Zé Trovão", "PL"),
        ("Fabio Schiochet", "UNIÃO"), ("Pedro Uczai", "PT"), ("Ana Paula Lima", "PT"), ("Cobalchini", "MDB"),
        ("Carlos Chiodini", "MDB"), ("Pezenti", "MDB"), ("Ismael", "PSD"), ("Ricardo Guidi", "PSD"),
        ("Gilson Marques", "NOVO")]
dep_names = [d for d, _ in DEPS]
dep_party = np.array([pp for _, pp in DEPS])
idx = {i: k for k, i in enumerate(m.ibge_id)}
pix_dm = np.zeros((N_DEP, 295))
for k, (name, party) in enumerate(DEPS):
    q = p[p.nome_parlamentar_emenda_plano_acao == name]
    if len(q):
        assert (q.cargo == "DEPUTADO FEDERAL").all(), name
        assert (q.partido_eleicao == party).all(), (name, q.partido_eleicao.unique())
    for ib, v in q.groupby("ibge_id").valor_plano.sum().items():
        pix_dm[k, idx[ib]] += v
sen = p[p.cargo == "SENADOR"]
pix_sen = np.zeros(295)
for ib, v in sen.groupby("ibge_id").valor_plano.sum().items():
    pix_sen[idx[ib]] += v
pix_dep_tot = pix_dm.sum(1)
LOW = pix_dep_tot < 10e6                       # Uczai, Marques, Ana Paula Lima
pooled = pix_dm[~LOW].sum(0) / pix_dm[~LOW].sum()
own_share = pix_dm / np.maximum(pix_dep_tot[:, None], 1)
# where deputies send the money: PPML of each deputy's plans on his or her share of the municipality's 2022 votes,
# population, GDP per capita and a co-partisan mayor, with deputy fixed effects (targeting.py), fit on the thirteen
# deputies with more than R$ 10 million; it imputes the geography of the three who used special transfers little
from targeting import vote_matrix, fit, shares
mayor_party = m.party_2024.replace({"PODE": "PODEMOS"}).values
gdp_pc = m.gdp_pc_2021.values
V22, T22 = vote_matrix(m.ibge_id.values, 2022, dep_names)
beta_t, se_t, _, n_t = fit(pix_dm, V22, T22, pop, gdp_pc, mayor_party, dep_party, ~LOW)
K_REC = int(np.median((pix_dm[~LOW] > 0).sum(1)))           # municipalities funded by the median deputy (29)
share = own_share.copy()
for k in np.where(LOW)[0]:
    share[k] = shares(beta_t, V22[k] / np.maximum(T22, 1), pop, gdp_pc, mayor_party == dep_party[k], K_REC)
alloc_main = QUOTA * share                                    # deputy x municipality, R$ per year
alloc_pooled_low = QUOTA * np.where(LOW[:, None], pooled[None, :], own_share)   # previous main specification
alloc_pooled = np.tile(QUOTA * pooled, (N_DEP, 1))
alloc_health = 0.5 * QUOTA * share + 0.5 * QUOTA * (pop / pop.sum())[None, :]
# the Chamber elected in 2026: re-elected deputies keep their geography; the newcomers' geography is imputed from their
# 2026 votes with the same model (federation partners count as co-partisans of the federation's main party)
TS = json.load(open(os.path.join(OUT, "tse_summary.json")))
reel = [r["pix_name"] for r in TS["deputies_2022"] if r["elected_2026"] == 1]
v26 = pd.read_csv(os.path.join(OUT, "tse_fed_2026.csv"))
el26 = v26[v26.elected == 1].groupby(["name", "party"]).votes.sum().reset_index()
old_full = set(v22n for v22n in pd.read_csv(os.path.join(OUT, "tse_fed_2022.csv")).query("elected == 1").name)
new26 = el26[~el26.name.isin(old_full)]
V26n, T26 = vote_matrix(m.ibge_id.values, 2026, list(new26.name), by="name")
rows26 = [share[dep_names.index(n)] for n in reel]
PMAP = {"PCDOB": "PT", "PODE": "PODEMOS"}
for k, (_, r) in enumerate(new26.iterrows()):
    rows26.append(shares(beta_t, V26n[k] / np.maximum(T26, 1), pop, gdp_pc, mayor_party == PMAP.get(r.party, r.party),
                         K_REC))
assert len(rows26) == N_DEP
alloc_2026 = QUOTA * np.array(rows26)
for a in (alloc_main, alloc_pooled_low, alloc_pooled, alloc_health, alloc_2026):
    assert abs(a.sum() - N_DEP * QUOTA) < 1.0
np.savez_compressed(os.path.join(OUT, "sq_alloc.npz"), main=alloc_main, pooled_low=alloc_pooled_low,
                    pooled=alloc_pooled, health=alloc_health, chamber2026=alloc_2026,
                    pix_dm=pix_dm, pix_sen=pix_sen, dep_party=dep_party, dep_names=np.array(dep_names),
                    low_pix=LOW, targeting_beta=beta_t, targeting_se=se_t)
m["x_sq"] = alloc_main.sum(0)
m["x_sq_pc"] = m.x_sq / pop
m["pix_dep"] = pix_dm.sum(0)
m["pix_dep_pc"] = m.pix_dep / pop

# ---------------------------------------------------------------- mayors
pan = pd.read_csv(os.path.join(C, "sc_mayors_panel_2016_2024.csv")).rename(columns={"cd_municipio_ibge": "ibge_id"})
inc = pd.read_csv(os.path.join(C, "sc_incumbency_2012_2024.csv")).rename(columns={"cod_ibge": "ibge_id"})
# crosswalk fix: the companion files map TSE 81507 (Santa Terezinha do Progresso) to IBGE 4215695 and TSE 81205
# (Santiago do Sul) to IBGE 4215687; IBGE codes are 4215687 and 4215695 respectively (TRE-SC totalization reports)
CW = {81507: 4215687, 81205: 4215695}
pan["ibge_id"] = [CW.get(t, i) for t, i in zip(pan.cd_municipio_tse, pan.ibge_id)]
inc["ibge_id"] = [CW.get(t, i) for t, i in zip(inc.cd_tse, inc.ibge_id)]
assert pan.ibge_id.is_unique and inc.ibge_id.is_unique
m = m.merge(pan[["ibge_id", "partido_2016", "partido_2020", "partido_2024", "margem_2024", "n_candidatos_2024",
                 "reeleito_2024_proxy"]], on="ibge_id", how="left", validate="one_to_one")
assert (m.partido_2024.replace({"PODE": "PODEMOS"}) == m.party_2024).all()
m["party"] = m.party_2024.replace({"PODE": "PODEMOS"})
# term-limited mayors in 2025-28 (re-elected in 2024) come from the old master (TRE-SC); compare with the proxy
agree = (m.term_limited_2025_28 == m.reeleito_2024_proxy.fillna(-1)).mean()

# ---------------------------------------------------------------- data moments
size_bins = [0, 5e3, 10e3, 20e3, 50e3, 100e3, 1e9]
size_lab = ["<5k", "5-10k", "10-20k", "20-50k", "50-100k", ">100k"]
m["size_class"] = pd.cut(pop, size_bins, labels=size_lab, right=False)
g = m.groupby("size_class", observed=True)
stats = {
    "n_mun": 295, "pop": float(pop.sum()),
    "rev_impute_r2": float(r2), "n_rev_imputed": int((~okr).sum()), "n_tax_imputed": int((~ok).sum()),
    "term_limited_agreement_with_proxy": float(agree),
    "pix_deputies_total": float(pix_dm.sum()), "pix_senators_total": float(pix_sen.sum()),
    "pix_deputy_totals": {n: float(v) for n, v in zip(dep_names, pix_dep_tot)},
    "low_pix_deputies": [n for n, l in zip(dep_names, LOW) if l],
    "targeting_ppml": {c: [float(b_), float(s_)] for c, b_, s_ in zip(["lvs", "lpop", "same", "lgdp"], beta_t, se_t)},
    "targeting_n": n_t, "reelected_2026": reel, "new_2026": list(new26.name), "recipients_median": K_REC,
    "sq_pc_by_size_mean": {k: float(v) for k, v in g.x_sq_pc.mean().items()},
    "sq_pc_by_size_popw": {k: float(v) for k, v in
                           g.apply(lambda d: d.x_sq.sum() / d.pop2022.sum(), include_groups=False).items()},
    "n_by_size": {k: int(v) for k, v in g.size().items()},
    "pix_zero_share": float((m.pix_dep == 0).mean()),
    "sq_zero_share": float((m.x_sq < 1).mean()),
    "corr_sqpc_need": float(np.corrcoef(m.x_sq_pc, m.need)[0, 1]),
    "corr_sqpc_need_popw": None,
    "state_pc": float(m.x_sq.sum() / pop.sum()),
}
w = pop / pop.sum()
mx, mn = np.average(m.x_sq_pc, weights=w), np.average(m.need, weights=w)
cov = np.average((m.x_sq_pc - mx) * (m.need - mn), weights=w)
stats["corr_sqpc_need_popw"] = float(cov / np.sqrt(np.average((m.x_sq_pc - mx) ** 2, weights=w) *
                                                    np.average((m.need - mn) ** 2, weights=w)))


def gini_w(x, w):
    o = np.argsort(x)
    x, w = x[o], w[o] / w.sum()
    cw = np.cumsum(w)
    cxw = np.cumsum(x * w) / np.sum(x * w)
    return float(1 - np.sum(w * (cxw + np.concatenate([[0], cxw[:-1]]))))


stats["gini_sq_pc_popw"] = gini_w(m.x_sq_pc.values, pop)
# the status-quo variants used in the robustness checks: amendments per inhabitant in the smallest and largest
# classes, concentration and need-targeting (the neediest fifth: lowest GDP per capita, up to 20% of the population,
# as in cc2_model.py)
o_ = np.argsort(m.need.values)[::-1]
cp_ = np.cumsum(pop[o_]) / pop.sum()
top_ = o_[cp_ <= 0.2 + 1e-12]
small, large = (m.size_class == "<5k").values, (m.size_class == ">100k").values
stats["sq_variants"] = {}
for nm_, al_ in (("main", alloc_main), ("pooled_low", alloc_pooled_low), ("pooled", alloc_pooled),
                 ("health", alloc_health), ("chamber2026", alloc_2026)):
    x_ = al_.sum(0)
    stats["sq_variants"][nm_] = {
        "pc_lt5k": float(x_[small].sum() / pop[small].sum()), "pc_gt100k": float(x_[large].sum() / pop[large].sum()),
        "gini_popw": gini_w(x_ / pop, pop), "zero_share": float((x_ < 1).mean()),
        "neediest_fifth_ratio": float(x_[top_].sum() / x_.sum() / (pop[top_].sum() / pop.sum()))}
# own-party targeting by deputies (value-weighted share to municipalities whose 2024 mayor is of the deputy's party)
own = [];
expc = []
for k in range(N_DEP):
    if LOW[k]:
        continue
    same = (m.party.values == dep_party[k])
    own.append((pix_dm[k] * same).sum());
    expc.append(pix_dep_tot[k] * same.mean())
stats["own_party_share_value"] = float(sum(own) / pix_dm[~LOW].sum())
stats["own_party_share_expected_count"] = float(sum(expc) / pix_dm[~LOW].sum())
# mayors' dynamics (SC, 2016-2024)
mp = {"DEM": "UNIÃO", "PSL": "UNIÃO", "PTB": "PRD", "PATRIOTA": "PRD", "PSC": "PODE", "PROS": "SOLIDARIEDADE"}
pan["p20m"] = pan.partido_2020.map(lambda x: mp.get(x, x))
pan["p16m"] = pan.partido_2016.map(lambda x: mp.get(x, x))
re24 = pan[pan.reeleito_2024_proxy == 1]
op24 = pan[pan.reeleito_2024_proxy == 0]
re20 = pan[pan.eleito_2020_igual_eleito_2016_cpf == 1]
op20 = pan[pan.eleito_2020_igual_eleito_2016_cpf == 0]
elig24 = inc[inc.lame_2021 == 0]
# open seats proper: the incumbent did not run (term-limited, or eligible and not running); seats of incumbents who ran
# and lost are not open seats (none of them stayed with the incumbent's party in 2020 or 2024)
pi_ = pan.merge(inc[["ibge_id", "lame_2017", "inc_ran_2020", "inc_won_2020", "lame_2021", "inc20_ran_2024",
                     "inc_won_2024"]], on="ibge_id", how="left", validate="one_to_one")
open20 = (pi_.lame_2017 == 1) | (pi_.inc_ran_2020 == 0)
open24 = (pi_.lame_2021 == 1) | (pi_.inc20_ran_2024 == 0)
lost20 = (pi_.lame_2017 == 0) & (pi_.inc_ran_2020 == 1) & (pi_.inc_won_2020 == 0)
lost24 = (pi_.lame_2021 == 0) & (pi_.inc20_ran_2024 == 1) & (pi_.inc_won_2024 == 0)
el20, el24 = inc.lame_2017 == 0, inc.lame_2021 == 0
ran20, ran24 = el20 & (inc.inc_ran_2020 == 1), el24 & (inc.inc20_ran_2024 == 1)
stats["mayors"] = {
    "run_2020": float(ran20.sum() / el20.sum()), "win_2020": float(inc.inc_won_2020[ran20].mean()),
    "run_2024": float(ran24.sum() / el24.sum()), "win_2024": float(inc.inc_won_2024[ran24].mean()),
    "n_eligible_2020": int(el20.sum()), "n_ran_2020": int(ran20.sum()),
    "n_eligible_2024": int(el24.sum()), "n_ran_2024": int(ran24.sum()),
    "switch_reelected_2020": float((re20.p16m != re20.p20m).mean()),
    "switch_reelected_2024": float((re24.p20m != re24.partido_2024).mean()),
    "open_kept_2020": float((pi_.p16m == pi_.p20m)[open20].mean()),
    "open_kept_2024": float((pi_.p20m == pi_.partido_2024)[open24].mean()),
    "n_open_2020": int(open20.sum()), "n_open_2024": int(open24.sum()),
    "lost_kept_2020": float((pi_.p16m == pi_.p20m)[lost20].mean()),
    "lost_kept_2024": float((pi_.p20m == pi_.partido_2024)[lost24].mean()),
    "open_kept_2020_all_not_reelected": float((op20.p16m == op20.p20m).mean()),
    "open_kept_2024_all_not_reelected": float((op24.p20m == op24.partido_2024).mean()),
    "switch_to_PL_2024_share_of_switchers": float(((re24.p20m != re24.partido_2024) & (re24.partido_2024 == "PL")).sum()
                                                  / (re24.p20m != re24.partido_2024).sum()),
    "PL_share_2020": float((pan.p20m == "PL").mean()), "PL_share_2024": float((pan.partido_2024 == "PL").mean()),
    "PL_share_open_2024": float((op24.partido_2024 == "PL").mean()),
    "lame_duck_share_2021_24": 118 / 289, "term_limited_share_2025_28": float(m.term_limited_2025_28.mean()),
    "party_shares_2016": pan.p16m.value_counts(normalize=True).round(4).to_dict(),
    "party_shares_2020": pan.p20m.value_counts(normalize=True).round(4).to_dict(),
    "party_shares_2024": pan.partido_2024.value_counts(normalize=True).round(4).to_dict(),
    "margin_2024_median": float(m.margem_2024.median()),
}
m.drop(columns=["partido_2024"]).to_csv(os.path.join(OUT, "sc_master2.csv"), index=False)
json.dump(stats, open(os.path.join(OUT, "data_stats.json"), "w"), indent=1, ensure_ascii=False)
print(json.dumps({k: v for k, v in stats.items() if k not in ("mayors",)}, indent=1, ensure_ascii=False)[:3000])
print(json.dumps(stats["mayors"], indent=1, ensure_ascii=False)[:1500])
