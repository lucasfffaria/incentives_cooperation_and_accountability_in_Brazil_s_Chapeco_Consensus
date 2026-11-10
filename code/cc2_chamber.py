# -*- coding: utf-8 -*-
"""Chamber module of CC-2: who list-makers select (Proposition 1), how deputies split effort (Proposition 2) and
how much brokerage survives the abolition of individual amendments (relocation, conde channel)."""
import numpy as np
from functools import lru_cache


@lru_cache(maxsize=None)
def top_mean(S, N, draws=400000, seed=3):
    """E[mean of the S largest of N iid N(0,1)] (Monte Carlo, cached)."""
    if N <= S:
        return 0.0
    rng = np.random.default_rng(seed + 1000 * S + N)
    x = rng.standard_normal((draws // N + 1, N))
    x.sort(axis=1)
    return float(x[:, -S:].mean())


def r_corr(t, s, rho):
    """Correlation between legislative skill and the selection index lambda_L + t lambda_B + s eps."""
    return (1 + t * rho) / np.sqrt(1 + t ** 2 + 2 * t * rho + s ** 2)


def r_corr_B(t, s, rho):
    return (t + rho) / np.sqrt(1 + t ** 2 + 2 * t * rho + s ** 2)


def chamber(P, seats, s_cond, eta_eff, closed, abolish):
    """P: parameter arrays [W]; seats [NP] (2022 seats); s_cond [W,NP] share of county money controlled by each
    party's condes; eta_eff [W] share of the abolished money re-created in discretionary channels."""
    W = len(P["s0"]);
    NP = len(seats)
    has = seats > 0
    s0, pi, ka = P["s0"], P["pi"], P["kappa"]
    t0, rho, se, sn = P["t0"], P["rho_LB"], P["sig_eps"], P["sig_nu"]
    # status quo: open list, effort share s0 on brokerage
    a = np.zeros((W, NP))
    for p in np.where(has)[0]:
        S = int(seats[p])
        Ns = np.ceil(P["k_asp"] * S).astype(int)
        cache = {n: top_mean(S, int(n)) for n in np.unique(Ns)}
        a[:, p] = [cache[n] for n in Ns]
    r_open = r_corr(t0, se, rho)
    if not closed:
        X = np.ones((W, NP));
        r_new = np.tile(r_open[:, None], (1, NP))
        psi = np.ones((W, NP))
    else:
        psi = (eta_eff[:, None] + P["chi_c"][:, None] * (1 - eta_eff[:, None]) * s_cond) if abolish else \
            np.ones((W, NP))
        X = pi[:, None] * psi / ka[:, None]
        r_new = r_corr(X * t0[:, None], sn[:, None], rho[:, None])
    eB = X * s0[:, None] / (X * s0[:, None] + 1 - s0[:, None])
    eL = 1 - eB
    skill_new = r_new * a
    skill_sq = r_open[:, None] * a
    g = P["gam_L"][:, None]
    w = seats / seats.sum()
    out_new = ((1 + g * skill_new) * eL * w).sum(1)
    out_sq = ((1 + g * skill_sq) * (1 - s0)[:, None] * w).sum(1)
    res = {
        "leg_effort": (eL * w).sum(1), "leg_effort_sq": 1 - s0,
        "leg_skill": (skill_new * w).sum(1), "leg_skill_sq": (skill_sq * w).sum(1),
        "leg_output": out_new / out_sq,
        "leg_output_sel_only": ((1 + g * skill_new) * (1 - s0)[:, None] * w).sum(1) / out_sq,
        "leg_output_eff_only": ((1 + g * skill_sq) * eL * w).sum(1) / out_sq,
        "X": X, "psi": psi, "eL_party": eL,
        "all_parties_gain": ((X < 1) | ~has[None, :]).all(1),
        "brok_skill": (r_corr_B(X * t0[:, None], sn[:, None], rho[:, None]) * a * w).sum(1) if closed else
        (r_corr_B(t0, se, rho)[:, None] * a * w).sum(1),
    }
    return res
