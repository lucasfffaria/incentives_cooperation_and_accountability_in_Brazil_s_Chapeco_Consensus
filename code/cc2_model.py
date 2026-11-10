# -*- coding: utf-8 -*-
"""CC-2: the model of the Chapeco Consensus. Vectorized over worlds (axis 0).

Modules: status quo (real 2025 Pix geography); Chamber (selection, effort, relocation; see cc2_chamber.py); counties
as a repeated game over three conde terms (2027-2038): election of the conde by the college of mayors, project
choice and approval (agenda setting), cooperation of mayors under private cost shocks, endogenous completion,
pre-election tilt, municipal elections with switching and bandwagon, targets and sanctions, value accounting.
Supplementary Material 02 gives the specification.
"""
import numpy as np
from scipy.special import expit, logit, gammaincinv
from scipy.stats import norm
from cc2_params import CONST, DESIGNS

T_TERMS = 3
EGRID = np.linspace(0.0, 1.0, 11)


def draw_random(W, geo, seed=1):
    """Common random numbers for a batch of W worlds (identical across designs)."""
    rng = np.random.default_rng(seed)
    T, J, K, M, NP = T_TERMS, geo.J, CONST["K"], geo.M, geo.P
    f4 = np.float32
    R = {
        "cost_g": rng.gamma(2.0, size=(W, T, J, K)).astype(f4),
        "sig_z": rng.standard_normal((W, T, J, K)).astype(f4),
        "host_u": rng.random((W, T, J, K)).astype(f4), "host_v": rng.random((W, T, J, K)).astype(f4),
        "theta_u": rng.random((W, T, J)).astype(f4), "comp_a": rng.standard_normal((W, T, J)).astype(f4),
        "vote_u": rng.random((W, T, M)).astype(f4), "tie_u": rng.random((W, T, J, NP)).astype(f4),
        "coop_u": rng.random((W, T, K, M)).astype(f4),
        "comp_u": rng.random((W, T, J, K)).astype(f4), "carry_u": rng.random((W, T, J, K)).astype(f4),
        "aband_u": rng.random((W, T, J, K)).astype(f4),
        "run_u": rng.random((W, T, M)).astype(f4), "win_u": rng.random((W, T, M)).astype(f4),
        "sw_u": rng.random((W, T, M)).astype(f4), "swd_u": rng.random((W, T, M)).astype(f4),
        "keep_u": rng.random((W, T, M)).astype(f4), "opd_u": rng.random((W, T, M)).astype(f4),
        "bw_u": rng.random((W, T, M)).astype(f4),
        "swing_u": rng.random((W, T, NP)),
        "xi": rng.standard_normal((W, T, J)).astype(f4),
        "align_u": rng.random((W, NP)).astype(f4),
    }
    return R


def elect_index(x, h):
    """Odd, concave-for-gains electoral index of a relative money change x (slope 1 at 0)."""
    return np.where(x >= 0, h * np.log1p(np.maximum(x, 0) / h), -h * np.log1p(np.maximum(-x, 0) / h))


def draw_party(u, share):
    """Categorical draw per (world, municipality) from shares [W, NP] with uniforms u [W, n]."""
    c = np.cumsum(share, axis=1)
    c = c / c[:, -1:]
    return (u[:, :, None] > c[:, None, :]).sum(-1).clip(0, share.shape[1] - 1)


def draw_party_excl(u, share, ex1, ex2):
    """As draw_party, excluding for each (world, municipality) the parties ex1 and ex2 [W, n] (the outgoing party
    cannot win a seat it lost or left open without keeping it)."""
    NP = share.shape[1]
    s = np.broadcast_to(share[:, None, :], ex1.shape + (NP,)).copy()
    ar = np.arange(NP)[None, None, :]
    s = np.where((ar == ex1[..., None]) | (ar == ex2[..., None]), 0.0, s)
    c = np.cumsum(s, axis=-1)
    c = c / np.maximum(c[..., -1:], 1e-12)
    return (u[..., None] > c).sum(-1).clip(0, NP - 1)


# --------------------------------------------------------------------------------------------- cooperation
def coop_equilibrium(Q, V, C, w, wt, part, hostm, stake, gt, dF, P, chi, iters=6):
    """Bayesian equilibrium of cooperation with logistic private cost shocks (mean-field over others' choices).

    Q [W,K] technical completion; V, C [W,K]; w, wt, part, hostm, stake [W,K,n]; gt [W,n] = 1 + gamma_tilde_m;
    dF [W,n] = delta_m * F_m (value of future participation); returns p [W,K,n], expected completion [W,K] and
    the expected share of co-financing collected [W,K]."""
    W, K, n = w.shape
    om, nuc, epx, ss = P["omega_h"][:, None], P["nu_c"][:, None, None], P["eps_x"][:, None, None], \
                       P["s_shock"][:, None, None]
    p = np.where(part, 0.7, 0.0)
    scale = np.maximum(ss * stake, 1e-9)
    for _ in range(iters):
        if chi > 0:
            A = (p * wt).sum(-1)
            Am = np.clip(A[..., None] - p * wt, 0, 1)
            Fk = ((1 - chi) + chi * A) ** nuc[..., 0]
            dq_c = (((1 - chi) + chi * np.clip(Am + wt, 0, 1)) ** nuc - ((1 - chi) + chi * Am) ** nuc)
        else:
            A = np.ones((W, K));
            Fk = np.ones((W, K));
            dq_c = np.zeros_like(w)
        Hk = 1 - om * (1 - (p * hostm).sum(-1))
        q = Q * Hk * Fk
        dq = Q[..., None] * (Hk[..., None] * dq_c + hostm * om[..., None] * Fk[..., None])
        qc = np.minimum(1.0, Q * Fk)[..., None] * np.where(hostm, 1.0, Hk[..., None])
        NG = gt[:, None, :] * w * V[..., None] * (dq + epx * qc) + dF[:, None, :] - stake
        pn = np.where(part, expit(NG / scale), 0.0)
        if chi == 0:
            pn = np.where(part & ~hostm, 1.0, pn)
        p = pn
    if chi > 0:
        A = (p * wt).sum(-1)
        Fk = ((1 - chi) + chi * A) ** P["nu_c"][:, None]
    else:
        A = np.ones((W, K));
        Fk = np.ones((W, K))
    Hk = 1 - P["omega_h"][:, None] * (1 - (p * hostm).sum(-1))
    return p, Q * Hk * Fk, A, Hk, Fk


def approval_ok(G, popn, rule):
    yes = G >= -1e-9
    n = G.shape[-1]
    okc = yes.sum(-1) > n / 2
    okp = (yes * popn[None, :]).sum(-1) > 0.5 * popn.sum()
    if rule == "count":
        return okc
    if rule == "pop":
        return okp
    return okc & okp


def build_coalition(G, popn, rule, ell):
    """Cheapest compensation that makes a majority approve; returns payments [W,n] (reais) and the coalition."""
    W, n = G.shape
    deficit = np.maximum(0, -G) / (1 + ell[:, None])
    yes = G >= -1e-9
    pay = np.zeros((W, n));
    coal = yes.copy()
    need_c = np.floor(n / 2) + 1
    need_p = 0.5 * popn.sum() + 1e-6
    for crit in (["count"] if rule == "count" else ["pop"] if rule == "pop" else ["count", "pop"]):
        if crit == "count":
            key = np.where(coal, np.inf, deficit)
        else:
            key = np.where(coal, np.inf, deficit / popn[None, :])
        order = np.argsort(key, axis=1)
        for r in range(n):
            mi = order[:, r]
            if crit == "count":
                short = coal.sum(1) < need_c
            else:
                short = (coal * popn[None, :]).sum(1) < need_p
            add = short & ~coal[np.arange(W), mi]
            pay[np.arange(W), mi] += np.where(add, deficit[np.arange(W), mi], 0)
            coal[np.arange(W), mi] |= add
    return pay, coal


# --------------------------------------------------------------------------------------------- main simulation
def simulate(P, design, geo, R, keep_mun=False):
    d = DESIGNS[design]
    W = len(P["s0"]);
    J, K, M, NP = geo.J, CONST["K"], geo.M, geo.P
    ar = np.arange(W)
    phi, chi = CONST["phi_cur"], (CONST["chi_cof"] if d["cofin"] else 0.0)
    lrg = d["lrg"]
    insp = (1 - P["p_I"]) * np.clip(1 - P["p_I"] * (1 + P["s_D"]), 0, None) if lrg else np.ones(W)
    ta = (P["g_TA"][:, None] * (1 - geo.kappa)[None, :]) if lrg else 0.0
    qm = np.minimum(1.0, P["q_loc0"][:, None] * (geo.kappa / geo.kbar)[None, :] ** P["nu"][:, None] * (1 + ta))

    def vloc(tl):
        dm = P["f_SC"][:, None] * np.where(tl, CONST["d_tl"], CONST["d_e"]) * insp[:, None]
        return (1 - dm) * (phi + (1 - phi) * (qm + (1 - qm) * P["v_inc"][:, None])), dm

    x_sq = geo.x_sq
    eps_x = P["eps_x"] + (1 - P["eps_x"]) * P["u_contract"] if d["contracts"] else P["eps_x"]
    gam = P["gam"] + P["gam_cb"] if d["cobrand"] else P["gam"]
    kap_cred = P["kap_cred"] * (1 - P["gam_cb"]) if d["cobrand"] else P["kap_cred"]
    Pc = dict(P);
    Pc["eps_x"] = eps_x
    counties = d["counties"]
    eta = np.ones(W) if not d["abolish"] else (P["eta_X"] * (1 - P["e_cap"]) if d["cap_disc"] else P["eta_X"])
    B_cty = (1 - eta) * geo.M_tot if counties else np.zeros(W)
    reloc = eta[:, None] * x_sq[None, :]                       # R$ per year still brokered (SQ geography)
    # ------------------------------------------------------------------ state
    party = np.tile(geo.party0, (W, 1));
    tl = np.tile(geo.tl0, (W, 1))
    share = np.tile(geo.state_share0, (W, 1))
    cparty = np.full((W, J), -1);
    ctheta = np.ones((W, J));
    ccomp = np.zeros((W, J))
    ptenure = np.zeros((W, J), int);
    inc_run = np.zeros((W, J), bool)
    gains = np.zeros((W, M))
    smult = np.ones((W, J))
    pipe = {k: np.zeros((W, J, K)) for k in ("V", "spent", "q", "dc")}
    pipe["act"] = np.zeros((W, J, K), bool);
    pipe["host"] = np.zeros((W, J, K), int)
    if d["split"] == "need":
        base_sh = np.array([(geo.pop[i] * geo.need[i]).sum() for i in geo.members])
    else:
        base_sh = geo.pop_j.copy()
    base_sh = base_sh / base_sh.sum()
    aligned = R["align_u"] < 0.5                                # parties aligned with the federal government
    # ------------------------------------------------------------------ outputs
    val_m = np.zeros((W, M));
    val_sq_m = np.zeros((W, M))
    O = {k: np.zeros(W) for k in ("div_mun", "div_cty", "admin", "lrg_cost", "reg_spent", "reg_value",
                                  "reg_completed_cost", "reg_cost", "abandoned_cost", "cofin_paid", "tilt",
                                  "coop_num", "coop_den", "coop_tl_num", "coop_tl_den", "coop_el_num",
                                  "coop_el_den", "coop_opp_num", "coop_opp_den", "coop_al_num", "coop_al_den",
                                  "coop_small_num", "coop_small_den", "fail", "fail_poor", "fail_rich",
                                  "reappointed", "inc_ran", "effort", "unfinished_end", "salvage", "projects",
                                  "approval_bind", "theta_mean", "comp_reapp", "comp_out", "n_reapp", "n_out",
                                  "persist_fail_num", "persist_fail_den", "trap", "val_reloc", "cty_money", "div_sq",
                                  "val_proj_total", "money_transfers", "money_reloc", "el_runs", "el_elig", "effort_u",
                                  "scale_gain", "quality_gain", "conflict_loss",
                                  "el_wins", "el_sw", "el_open", "el_kept", "tv_party")}
    chist = np.full((W, T_TERMS, J), -1, dtype=np.int8)
    cshare = np.zeros((W, T_TERMS, NP));
    mshare = np.zeros((W, T_TERMS, NP))
    mayor_share = np.zeros((W, T_TERMS + 1, NP))
    for p_ in range(NP):
        mayor_share[:, 0, p_] = (party == p_).mean(1)
    fail_prev = np.zeros((W, J), bool)
    perf_prev = np.zeros((W, J))
    m_ref = s_ref = None
    poor = geo.cap_terc == 0;
    rich = geo.cap_terc == 2
    for tau in range(T_TERMS):
        v1, d1 = vloc(tl)                                          # value per real and diversion, first half
        # --------------------------------------------------------- 1. conde election
        same_person = np.zeros((W, J), bool);
        same_party = np.zeros((W, J), bool)
        if counties and d["conde"]:
            for j in range(J):
                idx = geo.members[j];
                pj = party[:, idx]
                wv = geo.pop[idx] / geo.pop[idx].sum() if d["college"] == "pop" else np.ones(len(idx))
                if d["technical"]:
                    keep = inc_run[:, j] & (tau > 0)
                    same_person[:, j] = keep;
                    same_party[:, j] = keep
                    cparty[:, j] = -1
                    continue
                present = np.zeros((W, NP), bool)
                present[np.repeat(ar, len(idx)), pj.ravel()] = True
                util = np.where(present[:, None, :], 0.0, -np.inf) + P["phi_P"][:, None, None] * (
                        pj[:, :, None] == np.arange(NP)[None, None, :])
                if tau > 0:
                    incp = cparty[:, j]
                    bonus = np.where(inc_run[:, j][:, None], P["rho_R"][:, None] * gains[:, idx], 0.0)
                    util = util + (np.arange(NP)[None, None, :] == incp[:, None, None]) * bonus[:, :, None]
                util = util - util.max(-1, keepdims=True)
                pr = np.exp(util);
                pr = pr / pr.sum(-1, keepdims=True)
                cum = np.cumsum(pr, -1)
                vote = (R["vote_u"][:, tau, idx][:, :, None] > cum).sum(-1).clip(0, NP - 1)
                tally = np.zeros((W, NP))
                np.add.at(tally, (np.repeat(ar, len(idx)), vote.ravel()), np.tile(wv, W))
                tally = tally + 1e-6 * R["tie_u"][:, tau, j, :] * present
                win = tally.argmax(1)
                if tau > 0:
                    same_party[:, j] = win == cparty[:, j]
                    same_person[:, j] = same_party[:, j] & inc_run[:, j]
                cparty[:, j] = win
            # types: kept if the same person continues
            newc = ~same_person
            th_new = P["theta_lo"][:, None] + (1 - P["theta_lo"][:, None]) * R["theta_u"][:, tau, :]
            ctheta = np.where(newc, 1.0 if d["technical"] else th_new, ctheta)
            ccomp = np.where(newc, R["comp_a"][:, tau, :], ccomp)
            ptenure = np.where(same_party, ptenure + 1, 1)
            if tau > 0:
                O["reappointed"] += same_person.sum(1)
                O["inc_ran"] += inc_run.sum(1)
                O["comp_reapp"] += (ccomp * same_person).sum(1);
                O["n_reapp"] += same_person.sum(1)
            for p_ in range(NP):
                cshare[:, tau, p_] = (cparty == p_).mean(1)
            chist[:, tau, :] = cparty
        # --------------------------------------------------------- 2. county money this term
        sh = base_sh[None, :] * smult
        if d["aligned_bonus"] and counties and not d["technical"]:
            al = aligned[ar[:, None], np.clip(cparty, 0, NP - 1)] & (cparty >= 0)
            sh = sh * (1 + CONST["bonus_aligned"] * al)
        sh = sh / sh.sum(1, keepdims=True)
        B_term = 4 * B_cty[:, None] * sh                       # [W,J]
        Bn = B_term * (1 - (P["c_adm"][:, None] if d["projects"] else 0.0))
        O["admin"] += (B_term - Bn).sum(1)
        O["cty_money"] += Bn.sum(1)
        if counties:
            for p_ in range(NP):
                mshare[:, tau, p_] = (sh * (cparty == p_)).sum(1)
        # --------------------------------------------------------- 3. carried-over projects
        if counties and tau > 0:
            ab_p = np.where(same_person, 0.0, np.where(same_party, P["a_same"][:, None], P["a_ab"][:, None]))
            for j in range(J):
                idx = geo.members[j]
                act = pipe["act"][:, j, :]
                if not act.any():
                    continue
                aband = act & (R["aband_u"][:, tau, j, :] < ab_p[:, j][:, None])
                cont = act & ~aband
                done = cont & (R["carry_u"][:, tau, j, :] < pipe["q"][:, j, :])
                salv = (aband | (cont & ~done))
                wk = benefit_w(geo, idx, pipe["host"][:, j, :], P["D0"])
                gain = (done * P["beta_d"][:, None] * pipe["V"][:, j, :] + salv * P["v_inc"][:, None] *
                        pipe["spent"][:, j, :]) * (1 - pipe["dc"][:, j, :])
                val_m[:, idx] += (gain[..., None] * wk).sum(1)
                O["reg_value"] += gain.sum(1)
                O["salvage"] += (salv * P["v_inc"][:, None] * pipe["spent"][:, j, :]).sum(1)
                O["abandoned_cost"] += (aband * pipe["spent"][:, j, :]).sum(1)
                O["reg_completed_cost"] += (done * pipe["spent"][:, j, :]).sum(1)
            pipe["act"][:] = False
        # --------------------------------------------------------- 4. targets: score weights and threshold
        if counties:
            capc = geo.cap_j if d["targets"] == "absolute" else geo.cap_j - np.array(
                [geo.cap_j[geo.cap_terc == c].mean() for c in geo.cap_terc])
            if "w_perf" in P:
                # targets on outcome indicators (robustness): the conde's delivery is a small, given share of the score
                wp, wn = P["w_perf"], P["w_noise"]
                wc = np.maximum(1 - wp - wn, 0.0)
            else:
                wc, wn = P["w_cap"], P["w_noise"]
                wp = np.maximum(0.1, 1 - wc - wn)
                tot = wc + wn + wp
                wc, wn, wp = wc / tot, wn / tot, wp / tot
            sd_base = np.sqrt(wc * capc.var() + wp + wn)
            zbar = norm.ppf(P["phi_c"]) * sd_base
            # mayors' expectation that the county meets its targets: its capacity and its delivery last term
            # (at the reference level in the first term); this is the feedback of Proposition 7
            fpass = norm.cdf((np.sqrt(wc)[:, None] * capc[None, :] + np.sqrt(wp)[:, None] * perf_prev - zbar[:, None])
                             / np.sqrt(wn)[:, None])
        # --------------------------------------------------------- 5. plans (all counties)
        plan = [None] * J
        if counties:
            for j in range(J):
                plan[j] = make_plan(j, tau, geo, P, Pc, R, d, chi, party, tl, cparty, ctheta, ccomp, ptenure,
                                    inc_run, Bn, v1, qm, gam, kap_cred, insp, ta, O, fpass=fpass[:, j])
        # --------------------------------------------------------- reference for targets (term 1, e = 0.5)
        if counties and tau == 0:
            D0j = np.stack([plan[j]["Dj"](0.5) for j in range(J)], 1)
            m_ref = D0j.mean(1)
            s_ref = np.maximum(D0j.std(1), 0.02)
        # --------------------------------------------------------- 6-8. effort, tilt, realization
        H1 = np.zeros((W, M));
        H2 = np.zeros((W, M))
        Dreal = np.zeros((W, J));
        g_val = np.zeros((W, M));
        rev_val = np.zeros((W, M))
        if counties:
            for j in range(J):
                pl = plan[j];
                idx = geo.members[j]
                mu_z = lambda e, pl=pl, j=j: np.sqrt(wc) * capc[j] + np.sqrt(wp) * (pl["Dj"](e) - m_ref) / s_ref
                ppass = lambda e, mu_z=mu_z: norm.cdf((mu_z(e) - zbar) / np.sqrt(wn))
                can_re = (not d["one_term"])
                best_u = np.full(W, -np.inf);
                e_star = np.zeros(W);
                u_star = np.zeros(W)
                th = ctheta[:, j]
                for e in EGRID:
                    soc, pol, S, qV = pl["dV"](e)
                    if d["technical"]:
                        pR = ppass(e)
                    elif can_re:
                        pR = expit(pl["b"] + P["rho_R"] * S) * (ppass(e) if d["bar"] else 1.0)
                    else:
                        pR = np.zeros(W)
                    # unmeasured quality effort: perfect substitute in cost (crowding out), closed form
                    eu = np.clip(th * P["alpha_u"] * qV / P["c_e"] - e, 0, 1)
                    U = th * (soc + P["alpha_u"] * eu * qV) + (1 - th) * pol + P["V_R"] * pR - \
                        P["c_e"] * (e + eu) ** 2 / 2
                    upd = U > best_u + 1e-12
                    best_u = np.where(upd, U, best_u);
                    e_star = np.where(upd, e, e_star);
                    u_star = np.where(upd, eu, u_star)
                O["effort_u"] += u_star / J
                O["effort"] += e_star / J
                res = realize(j, tau, geo, P, Pc, R, d, chi, pl, e_star, party, cparty, ctheta, inc_run, Bn,
                              x_sq, reloc, can_re, O, insp, u_star)
                H1[:, idx] += res["H1"];
                H2[:, idx] += res["H2"]
                val_m[:, idx] += res["val_proj"] - res["cofin_cost"] * v1[:, idx]
                Dreal[:, j] = res["Dreal"]
                g_val[:, idx] += res["val_proj"] - res["cofin_cost"] * v1[:, idx]
                rev_val[:, idx] += pl["R_m"]
                for k in ("V", "spent", "q", "dc", "act", "host"):
                    pipe[k][:, j, :] = res["pipe"][k]
        # --------------------------------------------------------- money flows, first half
        val_m += H1 * v1 + 2 * reloc * v1
        val_sq_m += 2 * x_sq[None, :] * v1
        O["div_mun"] += ((H1 + 2 * reloc) * d1).sum(1)
        O["div_sq"] += (2 * x_sq[None, :] * d1).sum(1)
        O["val_reloc"] += (2 * reloc * v1).sum(1)
        # --------------------------------------------------------- 9. municipal election (mid-term)
        x_rel = (H1 + 2 * reloc - 2 * x_sq[None, :]) / (2 * geo.rev[None, :]) if counties else np.zeros((W, M))
        party_new, tl_new, share, est = municipal_election(tau, P, R, geo, party, tl, share, x_rel, cparty,
                                                           counties, d["technical"])
        for k_, v_ in est.items():
            O[k_] += v_
        O["tv_party"] += 0.5 * np.abs(np.stack([(party_new == p_).mean(1) - (party == p_).mean(1)
                                                 for p_ in range(NP)], 1)).sum(1) / T_TERMS
        v2, d2 = vloc(tl_new)
        val_m += H2 * v2 + 2 * reloc * v2
        val_sq_m += 2 * x_sq[None, :] * v2
        O["div_mun"] += ((H2 + 2 * reloc) * d2).sum(1)
        O["div_sq"] += (2 * x_sq[None, :] * d2).sum(1)
        O["val_reloc"] += (2 * reloc * v2).sum(1)
        O["money_transfers"] += (H1 + H2).sum(1)
        O["money_reloc"] += 4 * reloc.sum(1)
        g_val += H1 * v1 + H2 * v2
        if lrg:
            O["lrg_cost"] += P["c_A"] * (4 * geo.M_tot)
        party, tl = party_new, tl_new
        for p_ in range(NP):
            mayor_share[:, tau + 1, p_] = (party == p_).mean(1)
        # --------------------------------------------------------- 10. targets and sanctions
        if counties:
            perf = (Dreal - m_ref[:, None]) / s_ref[:, None]
            perf_prev = perf
            z = np.sqrt(wc)[:, None] * capc[None, :] + np.sqrt(wp)[:, None] * perf + np.sqrt(wn)[:, None] * \
                R["xi"][:, tau, :]
            fail = z < zbar[:, None]
            O["fail"] += fail.mean(1) / T_TERMS
            O["fail_poor"] += fail[:, poor].mean(1) / T_TERMS
            O["fail_rich"] += fail[:, rich].mean(1) / T_TERMS
            if tau > 0:
                O["persist_fail_num"] += (fail & fail_prev).sum(1)
                O["persist_fail_den"] += fail_prev.sum(1)
            if tau == 2:
                O["trap"] += (fail & fail_prev).mean(1)
            fail_prev = fail
            if d["technical"]:
                inc_run = ~fail
            else:
                inc_run = np.full((W, J), not d["one_term"]) & (~fail if d["bar"] else True)
            if d["territorial"]:
                Phi = np.clip(1 - geo.need_j[None, :] ** P["varrho"][:, None] / P["Xi"][:, None], 0, 1)
                smult = 1 - P["s_T"][:, None] * Phi * fail
            else:
                smult = np.ones((W, J))
            O["n_out"] += (~inc_run).sum(1)
            O["comp_out"] += (ccomp * ~inc_run).sum(1)
            gains = np.where(rev_val > 0, g_val / np.maximum(rev_val, 1) - 1, 0.0)
    # ------------------------------------------------------------------ end of horizon: unfinished projects
    if counties:
        for j in range(J):
            act = pipe["act"][:, j, :]
            if not act.any():
                continue
            idx = geo.members[j]
            wk = benefit_w(geo, idx, pipe["host"][:, j, :], P["D0"])
            ev = act * (1 - pipe["dc"][:, j, :]) * (
                    (1 - 0.5 * P["a_ab"][:, None]) * (pipe["q"][:, j, :] * P["beta_d"][:, None] * pipe["V"][:, j, :]
                                                      + (1 - pipe["q"][:, j, :]) * P["v_inc"][:, None] *
                                                      pipe["spent"][:, j, :])
                    + 0.5 * P["a_ab"][:, None] * P["v_inc"][:, None] * pipe["spent"][:, j, :])
            val_m[:, idx] += (ev[..., None] * wk).sum(1)
            O["reg_value"] += ev.sum(1)
            O["unfinished_end"] += (act * pipe["spent"][:, j, :]).sum(1)
    # ------------------------------------------------------------------ summary
    pop = geo.pop
    lrg_cost = O["lrg_cost"]
    # the commissioners cost a share of the money they oversee: charged in proportion to the value each
    # municipality receives (close to the money it receives)
    val_m -= lrg_cost[:, None] * val_m / np.maximum(val_m.sum(1, keepdims=True), 1)
    out = dict(O)
    out["cparty_hist"] = chist
    out["cond_party_share"] = cshare;
    out["cond_money_share"] = mshare;
    out["mayor_share"] = mayor_share
    out["eta_eff"] = eta
    out["val_m"] = val_m
    out["val_sq_internal_m"] = val_sq_m
    return out


def benefit_w(geo, idx, host, D0):
    """Benefit shares [W,K,n] of projects hosted at `host` [W,K] (global indices) among county members idx."""
    dd = geo.dist[host][..., idx]                              # [W,K,n]
    w = geo.pop[idx][None, None, :] * np.exp(-dd / D0[:, None, None])
    return w / w.sum(-1, keepdims=True)


def make_plan(j, tau, geo, P, Pc, R, d, chi, party, tl, cparty, ctheta, ccomp, ptenure, inc_run, Bn, v1, qm, gam,
              kap_cred, insp, ta, O, fpass=None):
    W = len(P["s0"]);
    K = CONST["K"];
    idx = geo.members[j];
    n = len(idx);
    ar = np.arange(W)
    popn = geo.pop[idx]
    Bj = Bn[:, j]
    # menu
    cg = R["cost_g"][:, tau, j, :].astype(float)
    C = (P["s_bar"][:, None] if d["projects"] else 0.0) * Bj[:, None] * cg / cg.sum(1, keepdims=True)
    sig = np.maximum(P["sig_bar"][:, None] + P["sd_sig"][:, None] * R["sig_z"][:, tau, j, :], -0.5)
    V = (1 + sig) * C
    w_rand = np.sqrt(popn) / np.sqrt(popn).sum()
    loc = np.minimum((R["host_v"][:, tau, j, :][..., None] > np.cumsum(w_rand)[None, None, :]).sum(-1), n - 1)
    host = np.where(R["host_u"][:, tau, j, :] < P["p_polo"][:, None], geo.polo[j], idx[loc])
    w = benefit_w(geo, idx, host, P["D0"])
    hostm = host[..., None] == idx[None, None, :]
    part = (w >= CONST["w_min"]) | hostm
    wt = np.where(part, w, 0.0)
    wt = wt / wt.sum(-1, keepdims=True)
    ell = P["ell"]
    stake = np.where(part, (1 + ell)[:, None, None] * chi * C[..., None] * wt, 0.0) + hostm * P["c_host"][:, None,
                                                                                            None] * C[..., None]
    # mayors' credit factor (opposition discount)
    cp = cparty[:, j]
    opp = (party[:, idx] != cp[:, None]) & (cp[:, None] >= 0)
    gt = 1 + gam[:, None] - P["zeta_opp"][:, None] * opp
    # horizon: stay in office x continuity of the conde's office
    pstay = np.where(tl[:, idx], 0.0, (P["r_run"] * P["p_win0"])[:, None])
    if d["technical"]:
        f_stay = fpass if fpass is not None else 1 - P["phi_c"]
        pwin_next = np.ones(W)
        b = np.zeros(W)
        sup = np.zeros(W)
        piv = np.zeros(W)
    else:
        wv = popn / popn.sum() if d["college"] == "pop" else np.ones(n) / n
        same = (party[:, idx] == cp[:, None])
        n_c = (same * wv).sum(1)
        rival = np.zeros(W)
        for p_ in range(geo.P):
            rival = np.maximum(rival, np.where(p_ != cp, ((party[:, idx] == p_) * wv).sum(1), 0))
        rho_ret = P["r_run"] * P["p_win0"] * (1 - P["h_sw"]) + (1 - P["r_run"] * P["p_win0"]) * P["r_keep"]
        mu_L = (n_c - rival) * rho_ret
        sd_L = np.sqrt(0.5 * (wv ** 2).sum())
        pwin_next = norm.cdf(mu_L / sd_L)
        b = logit(np.clip(pwin_next, 0.02, 0.98))
        sup = n_c
        piv = norm.pdf(mu_L / sd_L) / sd_L
        f_bar = fpass if fpass is not None else 1 - P["phi_c"]
        f_stay = np.zeros(W) if d["one_term"] else (f_bar if d["bar"] else np.ones(W))
    # continuity of the conde's office: the same conde, or a co-partisan successor who honours commitments
    p_person = pwin_next * f_stay
    p_party_new = pwin_next * (1 - f_stay)
    pcont = p_person + P["kap_party"] * p_party_new
    abar_ex = (1 - pwin_next) * P["a_ab"] + p_party_new * P["a_same"]
    can_re = not d["one_term"]
    beta4 = P["beta_y"] ** 4
    Dc = P["D_max"] * (1.0 if (can_re or d["technical"]) else 0.0) * np.clip(1 - sup / CONST["sup_safe"], 0, 1)
    d_c = P["d_c0"] * (1 - Dc) * (1 + P["g_ten"] * (ptenure[:, j] - 1)) * insp
    kj = geo.kappa_j[j] + P["g_pool"] * (1 - geo.kappa_j[j])
    ta_j = (P["g_TA"] * (1 - kj)) if d["lrg"] else 0.0
    Q0 = P["q_loc0"] * (1 - P["phi_cx"]) * (kj / geo.kbar) ** P["nu"] * (1 + P["alpha_a"] * ccomp[:, j]) * (1 + ta_j)

    def Qe(e):
        return np.clip(Q0 * (1 + P["alpha_e"] * e), 0, 1)[:, None] * np.ones((1, K))

    vbar = (v1[:, idx] * popn).sum(1) / popn.sum()
    # pass 1: equilibrium on the menu (future value from projects with sigma > 0)
    F_m = (gt[:, None, :] * w * V[..., None] * Qe(0.5)[..., None] * (sig > 0)[..., None]).sum(1)
    dF = beta4[:, None] * pstay * pcont[:, None] * F_m
    p, qx, A, Hk, Fk = coop_equilibrium(Qe(0.5), V, C, w, wt, part, hostm, stake, gt, dF, Pc, chi)
    CU = (1 - chi) * C
    spent = CU + chi * C * A
    th = ctheta[:, j][:, None]

    abar = abar_ex[:, None]

    def unfinished_value(q, spent):
        """Expected value of an unfinished project: continued (completes next term w.p. q) or abandoned."""
        return (1 - abar) * (q * P["beta_d"][:, None] * V + (1 - q) * P["v_inc"][:, None] * spent) + \
               abar * P["v_inc"][:, None] * spent

    def valuation(p, qx, A):
        spent = CU + chi * C * A
        EV = (1 - d_c)[:, None] * (qx * V + (1 - qx) * unfinished_value(qx, spent))
        soc = EV - vbar[:, None] * spent
        pol = ((gt[:, None, :] * w * V[..., None] * qx[..., None] - p * stake).sum(-1) / (1 + ell)[:, None]
               - CU + kap_cred[:, None] * CU)
        return th * soc + (1 - th) * pol

    U = valuation(p, qx, A)
    qx_menu, U_menu = qx.copy(), U.copy()
    ratio = np.where((U > 0) & (CU > 0), U / np.maximum(CU, 1e-9), -np.inf)
    order = np.argsort(-ratio, axis=1)
    cap_inv = 0.9 * Bj
    sel = np.zeros((W, K), bool)
    cum = np.zeros(W)
    for r in range(K):
        k = order[:, r]
        ok = (ratio[ar, k] > 0) & (cum + CU[ar, k] <= cap_inv)
        sel[ar, k] |= ok
        cum += np.where(ok, CU[ar, k], 0)
    # pass 2: equilibrium on the selected portfolio, approval
    for it in range(K + 1):
        F_m = (gt[:, None, :] * w * V[..., None] * Qe(0.5)[..., None] * sel[..., None]).sum(1)
        dF = beta4[:, None] * pstay * pcont[:, None] * F_m
        p, qx, A, Hk, Fk = coop_equilibrium(Qe(0.5), V, C, w, wt, part & sel[..., None], hostm & sel[..., None],
                                            stake * sel[..., None], gt, dF, Pc, chi)
        p = p * sel[..., None]
        L = Bj - (CU * sel).sum(1)
        R_m = Bj[:, None] * popn[None, :] / popn.sum()
        t0 = L[:, None] * popn[None, :] / popn.sum()
        G = (1 + ell)[:, None] * (t0 - R_m) + ((gt[:, None, :] * w * V[..., None] * qx[..., None] - p * stake)
                                               * sel[..., None]).sum(1)
        ok = approval_ok(G, popn, d["approval"]) | (sel.sum(1) == 0)
        if it == 0:
            bind0 = ~ok
        pay, coal = build_coalition(G, popn, d["approval"], ell)
        pay = np.where(ok[:, None], 0.0, pay)
        fin = np.where(coal, 0.0, t0)
        feas = ok | (pay.sum(1) <= fin.sum(1) + 1e-6)
        if feas.all():
            break
        # drop the lowest-ranked selected project where infeasible
        Usel = np.where(sel, U / CU, np.inf)
        drop = np.argmin(Usel, axis=1)
        sel[ar, drop] &= feas
    O["approval_bind"] += bind0 / geo.J / T_TERMS
    cut = np.where(coal, 0.0, t0) * (pay.sum(1) / np.maximum(fin.sum(1), 1e-9))[:, None]
    t_m = t0 + pay - np.where(ok[:, None], 0.0, cut)
    O["projects"] += sel.sum(1)

    def dV(e):
        """Conde's payoff components at measured effort e (term-budget units): social value (without quality),
        political value, mean retrospective gain of the college, and completed value (for quality effort)."""
        q_e = Qe(e) * Hk * Fk * sel
        sp = (CU + chi * C * A) * sel
        soc = ((1 - d_c)[:, None] * (q_e * V + (1 - q_e) * unfinished_value(q_e, sp)) * sel).sum(1) / np.maximum(Bj, 1)
        qV = ((1 - d_c)[:, None] * q_e * V).sum(1) / np.maximum(Bj, 1)
        pol = ((gt[:, None, :] * w * V[..., None] * q_e[..., None]).sum(-1).sum(1) / (1 + ell)) / np.maximum(Bj, 1)
        val_proj = ((1 - d_c)[:, None, None] * w * ((q_e * V + (1 - q_e) * unfinished_value(q_e, sp)) * sel)[..., None]
                    ).sum(1)
        gm = (t_m * v1[:, idx] + val_proj - (chi * C[..., None] * wt * p * sel[..., None]).sum(1) * v1[:, idx]) / \
             np.maximum(R_m * v1[:, idx], 1) - 1
        wv = popn / popn.sum() if d["college"] == "pop" else np.ones(n) / n
        return soc, pol, (gm * wv).sum(1), qV

    def Dj(e):
        q_e = Qe(e) * Hk * Fk * sel
        num = (CU * q_e).sum(1) + ((1 - CONST["phi_cur"]) * t_m * qm[:, idx]).sum(1)
        den = (CU * sel).sum(1) + ((1 - CONST["phi_cur"]) * t_m).sum(1)
        return num / np.maximum(den, 1e-9)

    out = dict(C=C, V=V, CU=CU, w=w, wt=wt, part=part, hostm=hostm, host=host, stake=stake, gt=gt, sel=sel, t_m=t_m,
               R_m=R_m * v1[:, idx], Q0=Q0, d_c=d_c, Dj=Dj, dV=dV, b=b, pstay=pstay, pcont=pcont, beta4=beta4,
               opp=opp, popn=popn, sup=sup, piv=piv, qx=qx, p_eq=p,
               qm_j=qm[:, idx], qx_menu=qx_menu, U_menu=U_menu, vbar=vbar, A_menu=A)
    return out


def realize(j, tau, geo, P, Pc, R, d, chi, pl, e_star, party, cparty, ctheta, inc_run, Bn, x_sq, reloc, can_re, O,
            insp, u_star):
    W = len(P["s0"]);
    K = CONST["K"];
    idx = geo.members[j];
    n = len(idx);
    ar = np.arange(W)
    sel = pl["sel"];
    C, V, CU, w, wt, part, hostm, stake, gt = (pl[k] for k in ("C", "V", "CU", "w", "wt", "part", "hostm", "stake",
                                                               "gt"))
    Q = np.clip(pl["Q0"] * (1 + P["alpha_e"] * e_star), 0, 1)[:, None] * np.ones((1, K))
    F_m = (gt[:, None, :] * w * V[..., None] * Q[..., None] * sel[..., None]).sum(1)
    dF = pl["beta4"][:, None] * pl["pstay"] * pl["pcont"][:, None] * F_m
    p, qx, A, Hk, Fk = coop_equilibrium(Q, V, C, w, wt, part & sel[..., None], hostm & sel[..., None],
                                        stake * sel[..., None], gt, dF, Pc, chi)
    p = p * sel[..., None]
    # cooperation draws
    coop = R["coop_u"][:, tau][:, :, idx] < p
    coop &= (part & sel[..., None])
    if chi > 0:
        Acol = (coop * wt).sum(-1)
        Fr = ((1 - chi) + chi * Acol) ** P["nu_c"][:, None]
    else:
        Acol = np.ones((W, K));
        Fr = np.ones((W, K))
    Hr = 1 - P["omega_h"][:, None] * (1 - (coop * hostm).sum(-1).clip(0, 1))
    q = Q * Hr * Fr * sel
    done = sel & (R["comp_u"][:, tau, j, :] < q)
    spent = (CU + chi * C * Acol) * sel
    d_c = pl["d_c"]
    Vq = V * (1 + P["alpha_u"] * u_star)[:, None]                    # value with unmeasured quality
    val_k = (1 - d_c)[:, None] * done * Vq
    # value decomposition and the cost of conflict (expected completion lost to obstruction and shortfalls)
    O["scale_gain"] += ((1 - d_c)[:, None] * done * (V - C)).sum(1)
    O["quality_gain"] += ((1 - d_c)[:, None] * done * (Vq - V)).sum(1)
    O["conflict_loss"] += ((1 - d_c)[:, None] * (Q - q) * sel * np.maximum(V - P["v_inc"][:, None] * CU, 0)).sum(1)
    val_proj = (val_k[..., None] * w).sum(1)
    cofin = (chi * C[..., None] * wt * coop).sum(1)
    # stats
    O["coop_num"] += (p * (part & sel[..., None])).sum((1, 2));
    O["coop_den"] += (part & sel[..., None]).sum((1, 2))
    partsel = part & sel[..., None]
    tl_now = pl["pstay"] == 0
    O["coop_tl_num"] += (p * partsel * tl_now[:, None, :]).sum((1, 2))
    O["coop_tl_den"] += (partsel * tl_now[:, None, :]).sum((1, 2))
    O["coop_el_num"] += (p * partsel * ~tl_now[:, None, :]).sum((1, 2))
    O["coop_el_den"] += (partsel * ~tl_now[:, None, :]).sum((1, 2))
    opp = pl["opp"]
    O["coop_opp_num"] += (p * partsel * opp[:, None, :]).sum((1, 2))
    O["coop_opp_den"] += (partsel * opp[:, None, :]).sum((1, 2))
    O["coop_al_num"] += (p * partsel * ~opp[:, None, :]).sum((1, 2))
    O["coop_al_den"] += (partsel * ~opp[:, None, :]).sum((1, 2))
    small = (geo.pop[idx] < 10000)[None, None, :]
    O["coop_small_num"] += (p * partsel * small).sum((1, 2))
    O["coop_small_den"] += (partsel * small).sum((1, 2))
    O["reg_spent"] += spent.sum(1);
    O["reg_cost"] += (CU * sel).sum(1)
    O["reg_value"] += val_k.sum(1)
    O["reg_completed_cost"] += (spent * done).sum(1)
    O["cofin_paid"] += cofin.sum(1)
    O["div_cty"] += (d_c[:, None] * spent).sum(1)
    O["theta_mean"] += ctheta[:, j] / geo.J / T_TERMS
    # pipeline: unfinished projects
    unf = sel & ~done
    pipe = dict(V=np.where(unf, Vq, 0), spent=np.where(unf, spent, 0), q=np.where(unf, q, 0),
                dc=np.where(unf, d_c[:, None], 0), act=unf, host=pl["host"])
    # transfers by half; pre-election tilt in the first half
    t_m = pl["t_m"]
    H1 = t_m / 2;
    H2 = t_m / 2
    cp = cparty[:, j]
    if (not d["technical"]) and can_re:
        co = (party[:, idx] == cp[:, None])
        # incumbent party's win probability in co-partisan municipalities
        pw = np.where(pl["pstay"] > 0, (P["r_run"] * P["p_win0"] + (1 - P["r_run"] * P["p_win0"]) * P["r_keep"]
                                        )[:, None], P["r_keep"][:, None])
        wv = pl["popn"] / pl["popn"].sum() if d["college"] == "pop" else np.ones(n) / n
        A_m = (P["V_R"] * pl["piv"])[:, None] * wv[None, :] * pw * (1 - pw) * P["alpha_V"][:, None] * \
              P["h_V"][:, None] * co
        lam = ctheta[:, j] * P["c_T"] / np.maximum(Bn[:, j], 1)
        rev2 = 2 * geo.rev[idx][None, :]
        Tm = np.where(lam[:, None] > 0, np.maximum(A_m / np.maximum(lam[:, None], 1e-30) - P["h_V"][:, None] * rev2,
                                                   0), np.where(A_m > 0, np.inf, 0))
        Tmax = 0.5 * (H1 * ~co).sum(1)
        tot = np.where(np.isinf(Tm).any(1), np.inf, Tm.sum(1))
        scale = np.where(tot > Tmax, Tmax / np.where(np.isinf(tot), 1, np.maximum(tot, 1e-9)), 1.0)
        Tfin = np.where(np.isinf(Tm), 0.0, Tm) * scale[:, None]
        Tm = np.where(np.isinf(tot)[:, None], Tmax[:, None] * A_m / np.maximum(A_m.sum(1, keepdims=True), 1e-30),
                      Tfin)
        Tm = np.nan_to_num(Tm)
        cutv = (H1 * ~co) * (Tm.sum(1) / np.maximum((H1 * ~co).sum(1), 1e-9))[:, None]
        H1 = H1 + Tm - cutv
        O["tilt"] += Tm.sum(1)
    qmj = pl["qm_j"]
    Dreal = ((CU * done).sum(1) + ((1 - CONST["phi_cur"]) * t_m * qmj).sum(1)) / np.maximum(
        (CU * sel).sum(1) + ((1 - CONST["phi_cur"]) * t_m).sum(1), 1e-9)
    return dict(H1=H1, H2=H2, val_proj=val_proj, cofin_cost=cofin, Dreal=Dreal, pipe=pipe)


def municipal_election(tau, P, R, geo, party, tl, share, x_rel, cparty, counties, technical):
    W, M = party.shape;
    NP = geo.P;
    ar = np.arange(W)
    # statewide partisan climate at this election: a Dirichlet draw (no compounding) whose mean keeps the expected party
    # composition at its 2024 level when seats that change hands go to another party (Geo.climate0)
    a_ = np.maximum(P["c_dir"][:, None] * geo.climate0[None, :], 1e-3)
    G = gammaincinv(a_, np.clip(R["swing_u"][:, tau, :], 1e-12, 1 - 1e-12))
    share = G / G.sum(1, keepdims=True)
    cp_m = cparty[:, geo.cty] if (counties and not technical) else np.full((W, M), -1)
    has_c = cp_m >= 0
    g = elect_index(x_rel, P["h_V"][:, None])
    eligible = ~tl
    runs = eligible & (R["run_u"][:, tau] < P["r_run"][:, None])
    # switching before running: to the conde's party with prob beta_bw, else state shares
    sw_ = runs & (R["sw_u"][:, tau] < P["h_sw"][:, None])
    dest = draw_party(R["swd_u"][:, tau], share)
    to_c = has_c & (R["bw_u"][:, tau] < P["beta_bw"][:, None])
    newp_sw = np.where(to_c, cp_m, dest)
    p_run = np.where(sw_, newp_sw, party)
    a_w = logit(P["p_win0"])[:, None]
    wins = runs & (R["win_u"][:, tau] < expit(a_w + P["alpha_V"][:, None] * g))
    # open seats (kept by the outgoing party with probability r_keep) and defeated incumbents: a seat that is not kept
    # goes to another party, the conde's with probability beta_bw, otherwise one drawn from the statewide climate
    keep = (~wins) & (R["keep_u"][:, tau] < expit(logit(P["r_keep"])[:, None] + P["alpha_V"][:, None] * g)) & ~runs
    other = draw_party_excl(R["opd_u"][:, tau], share, party, p_run)
    to_c2 = has_c & (R["bw_u"][:, tau] < P["beta_bw"][:, None]) & (cp_m != party) & (cp_m != p_run)
    newp = np.where(to_c2, cp_m, other)
    new_party = np.where(wins, p_run, np.where(keep, party, newp))
    new_tl = wins.copy()                                       # re-elected mayors become term-limited
    est = {"el_runs": runs.sum(1), "el_elig": eligible.sum(1), "el_wins": wins.sum(1),
           "el_sw": (wins & (p_run != party)).sum(1), "el_open": (~runs).sum(1), "el_kept": keep.sum(1)}
    return new_party, new_tl, share, est


def summarize(out, ref, geo, P):
    """Scorecard of one design relative to a reference run (normally SQ) in the same worlds."""
    val_m, val_r = out["val_m"], ref["val_m"]
    pop = geo.pop
    nz = geo.need[None, :] ** P["zeta"][:, None]
    S = {}
    S["val"] = val_m.sum(1);
    S["val_ref"] = val_r.sum(1)
    S["dval"] = 100 * (S["val"] / S["val_ref"] - 1)
    S["dval_need"] = 100 * ((val_m * nz).sum(1) / (val_r * nz).sum(1) - 1)
    pc = val_m / pop[None, :]
    S["gini"] = gini_rows(pc, pop)
    S["corr_need"] = wcorr_rows(pc, geo.need, pop)
    # share of value received by the neediest fifth of the population, relative to its population share
    o_ = np.argsort(-geo.need)
    cp_ = np.cumsum(pop[o_]) / pop.sum()
    top = np.zeros(len(pop), bool)
    top[o_[cp_ <= 0.2 + 1e-12]] = True
    S["need_top20_share"] = val_m[:, top].sum(1) / val_m.sum(1) / (pop[top].sum() / pop.sum())
    lose = val_m < val_r * (1 - 1e-9)
    S["lose_mun"] = lose.mean(1);
    S["lose_pop"] = (lose * pop).sum(1) / pop.sum()
    for c in ("<5k", "5-10k", "10-20k", "20-50k", "50-100k", ">100k"):
        msk = geo.size_class == c
        S["dval_size_" + c] = 100 * (val_m[:, msk].sum(1) / val_r[:, msk].sum(1) - 1)
    O = out
    S["coop"] = O["coop_num"] / np.maximum(O["coop_den"], 1)
    for s_ in ("tl", "el", "opp", "al", "small"):
        S["coop_" + s_] = O[f"coop_{s_}_num"] / np.maximum(O[f"coop_{s_}_den"], 1)
    S["reg_share"] = O["reg_cost"] / np.maximum(O["cty_money"], 1)
    S["completion"] = O["reg_completed_cost"] / np.maximum(O["reg_spent"], 1)
    S["persist_fail"] = O["persist_fail_num"] / np.maximum(O["persist_fail_den"], 1)
    S["reappoint_rate"] = O["reappointed"] / np.maximum(O["inc_ran"], 1)
    S["div_total"] = (O["div_mun"] + O["div_cty"]) / 12
    money12 = 12 * geo.M_tot
    for k in ("conflict_loss", "scale_gain", "quality_gain", "cofin_paid", "reg_value", "salvage", "abandoned_cost",
              "unfinished_end", "admin", "lrg_cost", "div_mun", "div_cty", "div_sq", "tilt", "reg_cost"):
        S["sh_" + k] = O[k] / money12
    S["conde_turnover"] = 1 - O["reappointed"] / (geo.J * (T_TERMS - 1))
    S["sel_competence"] = O["comp_reapp"] / np.maximum(O["n_reapp"], 1)
    S["effort"] = O["effort"] / T_TERMS
    S["effort_u"] = O["effort_u"] / T_TERMS
    for k in ("fail", "fail_poor", "fail_rich", "trap", "approval_bind", "tilt", "projects",
              "theta_mean", "abandoned_cost", "unfinished_end", "eta_eff"):
        S[k] = O[k]
    return S


def gini_rows(x, w):
    o = np.argsort(x, axis=1)
    xs = np.take_along_axis(x, o, 1);
    ws = w[o] / w.sum()
    cxw = np.cumsum(xs * ws, 1) / np.maximum((xs * ws).sum(1, keepdims=True), 1e-12)
    prev = np.concatenate([np.zeros((x.shape[0], 1)), cxw[:, :-1]], 1)
    return 1 - (ws * (cxw + prev)).sum(1)


def wcorr_rows(x, y, w):
    w = w / w.sum()
    mx = (x * w).sum(1, keepdims=True);
    my = (y * w).sum()
    cov = ((x - mx) * (y - my) * w).sum(1)
    return cov / np.sqrt(((x - mx) ** 2 * w).sum(1) * ((y - my) ** 2 * w).sum())
