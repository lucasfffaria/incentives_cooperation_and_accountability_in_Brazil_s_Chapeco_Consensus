# -*- coding: utf-8 -*-
"""Where deputies send their special transfers: a Poisson pseudo-maximum-likelihood model of the money each deputy
plans for each municipality, with deputy fixed effects, on the deputy's share of the municipality's votes in the
previous election, population, GDP per capita and whether the mayor belongs to the deputy's party. Used by
prep_data2.py (to impute the geography of deputies with little use of special transfers, and of the deputies
elected in 2026) and by electoral_connection.py (to report the estimates)."""
import os
import numpy as np, pandas as pd
import statsmodels.api as sm
from prep_tse import PIX_TO_TSE

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DER = os.path.join(ROOT, "data", "derived")
EPS = 1e-4          # added to vote shares before taking logs (a few municipality-deputy cells have no votes)


def vote_matrix(ids, year=2022, names=None, by="ballot", elected_only=True):
    """Votes [n_names x M] of the given candidates (Pix author names for 2022, full TSE names otherwise) and the
    total valid nominal votes for the Chamber in each municipality [M]."""
    v = pd.read_csv(os.path.join(DER, f"tse_fed_{year}.csv"))
    pos = {i: k for k, i in enumerate(ids)}
    T = np.zeros(len(ids))
    for i, x in v.groupby("ibge_id").votes_valid.sum().items():
        T[pos[i]] = x
    if names is None:
        return None, T
    w = v[v.elected == 1] if elected_only else v
    V = np.zeros((len(names), len(ids)))
    for k, n in enumerate(names):
        key = PIX_TO_TSE[n] if by == "ballot" else n
        col = "ballot_name" if by == "ballot" else "name"
        s = w[w[col] == key].groupby("ibge_id").votes_valid.sum()
        assert len(s), n
        for i, x in s.items():
            V[k, pos[i]] = x
    return V, T


def design(vs, pop, gdp_pc, same):
    return np.column_stack([np.log(vs + EPS), np.log(pop), same.astype(float), np.log(gdp_pc)])


COLS = ["lvs", "lpop", "same", "lgdp"]


def fit(pix_dm, V, T, pop, gdp_pc, mayor_party, dep_party, mask):
    """PPML with deputy fixed effects on the deputies in mask; standard errors clustered by municipality."""
    rows, y, dd, jj = [], [], [], []
    for d in np.where(mask)[0]:
        vs = V[d] / np.maximum(T, 1)
        rows.append(design(vs, pop, gdp_pc, mayor_party == dep_party[d]))
        y.append(pix_dm[d] / 1e6)
        dd += [d] * len(pop)
        jj += list(range(len(pop)))
    X = pd.DataFrame(np.vstack(rows), columns=COLS)
    X = pd.concat([X, pd.get_dummies(pd.Series(dd), prefix="d").astype(float)], axis=1)
    f = sm.GLM(np.concatenate(y), X, family=sm.families.Poisson()).fit(cov_type="cluster",
                                                                       cov_kwds={"groups": np.array(jj)})
    beta = np.array([f.params[c] for c in COLS])
    se = np.array([f.bse[c] for c in COLS])
    return beta, se, f, int(len(dd))


def shares(beta, vs, pop, gdp_pc, same, top_k=None):
    """Predicted shares of a deputy's money; with top_k, only the top_k municipalities by predicted money receive
    transfers (a deputy funds a limited number of municipalities: the median of the thirteen funds 29)."""
    z = design(vs, pop, gdp_pc, same) @ beta
    w = np.exp(z - z.max())
    if top_k is not None:
        w = np.where(w >= np.sort(w)[-top_k], w, 0.0)
    return w / w.sum()
