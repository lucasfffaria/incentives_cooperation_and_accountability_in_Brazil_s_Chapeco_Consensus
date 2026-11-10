# -*- coding: utf-8 -*-
"""Parameters (priors with sources), designs and samplers of the model (CC-2).

Every behavioural parameter of the new institutions is drawn from a uniform prior. Ranges anchored on evidence say
so in `src`; ranges marked "assumption" are not estimates. Groups are used for the grouped Sobol analysis.
"""
import numpy as np
from scipy.stats import qmc

# name: (lo, hi, group, description, source)
PRIORS = {
    # G1 Chamber: selection and effort
    "s0": (0.5, 0.8, "Chamber", "status-quo share of deputies' effort on brokerage", "premise P1; unmeasured"),
    "pi": (0.2, 1.2, "Chamber", "list-makers' weight on brokerage relative to voters'", "assumption"),
    "kappa": (0.5, 2.0, "Chamber", "list-makers' weight on legislation relative to voters'", "assumption"),
    "t0": (0.5, 2.0, "Chamber", "voters' weight on brokerage skill relative to legislative skill (open list)",
           "assumption"),
    "rho_LB": (-0.3, 0.5, "Chamber", "correlation between legislative and brokerage skill", "assumption"),
    "sig_eps": (1.0, 3.0, "Chamber", "noise in personal votes, relative to the weight on legislative skill",
                "assumption"),
    "sig_nu": (0.5, 3.0, "Chamber", "list-makers' idiosyncratic criteria (loyalty, faction)",
               "assumption; Jones et al. (2002)"),
    "k_asp": (2.0, 5.0, "Chamber", "serious aspirants per seat", "assumption"),
    "gam_L": (0.1, 0.3, "Chamber", "legislative productivity per SD of legislative skill", "assumption"),
    # G2 relocation of brokerage
    "eta_X": (0.0, 1.0, "Relocation", "share of abolished amendment money re-created in discretionary channels",
              "Rapporteur-amendment (RP9) episode 2022-23: half to individual amendments, half to ministries; committee amendments "
              "R$0.3 bn (2022) to R$6.9 bn (2023) and R$14.2 bn (2024) (Ronconi et al. 2025)"),
    "chi_c": (0.0, 1.0, "Relocation", "responsiveness of a co-partisan conde to deputies' requests", "assumption"),
    # G3 regional projects
    "s_bar": (0.3, 1.0, "Projects", "cost of candidate regional projects / county money of a term", "assumption"),
    "sig_bar": (-0.1, 0.3, "Projects", "mean net scale economies of regional projects",
                "Bel & Warner (2015); Bel & Sebő (2021)"),
    "sd_sig": (0.1, 0.3, "Projects", "dispersion of scale economies across projects", "assumption"),
    "p_polo": (0.4, 0.8, "Projects", "probability that a project is hosted by the county's largest city",
               "assumption"),
    "D0": (30.0, 90.0, "Projects", "distance decay of project benefits (km)", "assumption"),
    "c_host": (0.0, 0.10, "Projects", "host's local cost (land, permits, opposition), share of project cost",
               "assumption"),
    "kap_cred": (0.0, 0.3, "Projects", "conde's private credit per real of regional investment",
                 "assumption; Litschig (2012) credit logic"),
    # G4 implementation
    "q_loc0": (0.55, 0.80, "Implementation", "completion of transfer-funded municipal works within a term",
               "TCU (2019): 37.5% paralyzed or unfinished; TCU (2023): 41% (SC 38.9%)"),
    "nu": (0.0, 0.3, "Implementation", "elasticity of completion to technical capacity",
           "2025 special transfers to SC: planned value with technical impediments 23% (<5,000 inh.) to 10-12% "
           "(20,000-100,000); implied elasticity 0.13-0.17"),
    "phi_cx": (0.0, 0.3, "Implementation", "completion penalty of regional (complex) projects", "assumption"),
    "g_pool": (0.0, 0.5, "Implementation", "share of the capacity gap closed by a county technical team",
               "assumption"),
    "alpha_e": (0.1, 0.5, "Implementation", "proportional gain in completion at full supervision effort",
                "assumption"),
    "c_e": (0.02, 0.2, "Implementation", "conde's cost of full effort (share of term budget)", "assumption"),
    "v_inc": (0.1, 0.5, "Implementation", "salvage value of an abandoned work per real", "assumption"),
    "a_ab": (0.2, 0.6, "Implementation", "abandonment of unfinished projects when the conde's party changes",
             "assumption; disruption after turnover (Akhtari et al. 2022)"),
    "a_same": (0.0, 0.2, "Implementation", "abandonment when the conde changes within the same party",
               "assumption"),
    "beta_d": (0.7, 0.9, "Implementation", "value of a work completed one term late, per real of on-time value",
               "assumption"),
    "c_adm": (0.01, 0.04, "Implementation", "county administration, share of county money", "assumption"),
    "alpha_u": (0.0, 0.2, "Implementation", "value gain of completed projects from unmeasured quality effort",
                "assumption; multitask (Holmstrom & Milgrom 1991)"),
    "alpha_a": (0.0, 0.15, "Implementation", "completion gain per SD of the conde's competence", "assumption"),
    # G5 cooperation
    "omega_h": (0.2, 0.6, "Cooperation", "completion lost if the host obstructs", "assumption"),
    "nu_c": (1.0, 3.0, "Cooperation", "elasticity of completion to the share of the project's cost funded",
             "assumption; TCU: insufficient counterpart funds"),
    "eps_x": (0.0, 0.5, "Cooperation", "excludability of benefits / enforcement against non-payers",
              "assumption; Law 11.107/2005 (exclusion of defaulting members)"),
    "zeta_opp": (0.0, 0.4, "Cooperation", "discount on benefits credited to a rival party's conde",
                 "assumption; alignment and adoption (Macinko et al. 2010)"),
    "s_shock": (0.25, 1.0, "Cooperation", "scale of private cost shocks relative to the mayor's stake",
                "assumption"),
    "ell": (0.0, 0.5, "Cooperation", "mayors' localism premium", "Gerber & Gibson (2009); Ten Cate (2023)"),
    "gam": (0.0, 0.3, "Cooperation", "credit for regional projects accruing to participating mayors",
            "assumption"),
    "beta_y": (0.85, 0.95, "Cooperation", "annual discount factor", "assumption"),
    # G6 conde politics
    "theta_lo": (0.2, 0.7, "Conde", "lower bound of condes' weight on value (theta ~ U[theta_lo, 1])",
                 "assumption"),
    "V_R": (0.0, 0.3, "Conde", "value of reappointment to the conde, share of term budget", "assumption"),
    "rho_R": (0.0, 3.0, "Conde", "retrospective weight of mayors' gains in the college vote (logit)",
              "assumption; Ferraz & Finan (2008) for voters"),
    "phi_P": (1.5, 4.0, "Conde", "party loyalty in the college vote (logit)",
              "Novaes (2018): 31-39% of mayors switch parties"),
    "kap_party": (0.3, 1.0, "Conde", "share of a conde's commitments honored by a co-partisan successor",
                  "assumption"),
    "c_T": (0.0, 0.5, "Conde", "conde's cost per real moved in the pre-election tilt", "assumption"),
    "alpha_V": (0.5, 6.0, "Conde", "electoral return to local money (logit per unit of revenue)",
                "Litschig & Morrison (2013): +10 points of incumbent-party re-election (base 0.17) for 20% more spending; about 3.5 logit points per unit (conversion in Section S4.8; 95% interval about 0.1-5.9)"),
    "h_V": (0.02, 0.10, "Conde", "scale of diminishing electoral returns (share of revenue)", "assumption"),
    # G7 municipal dynamics
    "r_run": (0.690, 0.708, "Municipal", "eligible incumbents who run", "SC 2020: 0.690; 2024: 0.708"),
    "p_win0": (0.669, 0.742, "Municipal", "incumbents who run and win", "SC 2024: 0.669; 2020: 0.742"),
    "h_sw": (0.18, 0.45, "Municipal", "switching hazard of running incumbents",
             "calibrated: re-elected mayors who changed party, SC 2020: 0.136; 2024: 0.349"),
    "beta_bw": (0.0, 0.3, "Municipal", "bandwagon toward the conde's party (switchers and open seats)",
                "assumption; 62% of 2024 switchers joined the governor's party"),
    "r_keep": (0.148, 0.185, "Municipal", "open seats kept by the outgoing mayor's party",
               "SC 2020: 0.148; 2024: 0.185 (incumbent not running)"),
    "c_dir": (10.0, 40.0, "Municipal", "precision of the statewide partisan climate at each election (Dirichlet)",
              "calibrated: change in mayors' party shares, SC 2016-20: 0.15; 2020-24: 0.23"),
    # G8 diversion and capture
    "f_SC": (0.5, 1.0, "Diversion", "Santa Catarina factor on municipal diversion rates",
             "Ferraz & Finan (2011): 0.055 eligible, 0.074 term-limited"),
    "d_c0": (0.04, 0.12, "Diversion", "baseline diversion and capture in county procurement",
             "Ferraz & Finan (2011); lower part of the 5-23% model-implied corruption tax on firms in Colonnelli & Prem (2022)"),
    "D_max": (0.15, 0.5, "Diversion", "discipline from a contestable reappointment",
              "Ferraz & Finan (2011): 27-36%"),
    "g_ten": (0.0, 0.3, "Diversion", "rise in capture per extra term of party tenure", "assumption"),
    # G9 targets and sanctions
    "w_cap": (0.3, 0.6, "Targets", "share of capacity in the county score", "assumption"),
    "w_noise": (0.2, 0.5, "Targets", "share of noise in the county score", "Kane & Staiger (2002)"),
    "phi_c": (0.1, 0.3, "Targets", "share of counties failing at baseline", "design (open in the proposal)"),
    "s_T": (0.2, 0.6, "Targets", "share of next-term money withheld from a failing county",
            "design (proposal: loss of access to new resources)"),
    "Xi": (1.5, 3.0, "Targets", "Union's resolve to enforce territorial sanctions", "assumption"),
    "varrho": (0.5, 1.5, "Targets", "need gradient of the harm from withholding money", "assumption"),
    # G10 managerial law
    "p_I": (0.0, 0.3, "LRG", "efficacy of inspection (share of attempts blocked)",
            "Olken (2007); Avis et al. (2018)"),
    "s_D": (0.0, 2.0, "LRG", "penalty per real when diversion is detected", "assumption"),
    "g_TA": (0.0, 0.3, "LRG", "completion gain from technical assistance at zero capacity",
             "Lautharte et al. (2021); companion paper"),
    "c_A": (0.0, 0.03, "LRG", "cost of commissioners per real overseen", "companion paper: R$350k per year"),
    # G11 inequality aversion
    "zeta": (0.0, 1.0, "Need", "inequality aversion in need-weighted value", "assumption"),
    # design-specific magnitudes (used only by the designs that need them)
    "u_contract": (0.5, 0.9, "Design", "share of non-excludable benefit made enforceable by contracts (R3)",
                   "assumption; Kresch (2020)"),
    "gam_cb": (0.3, 0.7, "Design", "credit shared with participating mayors under co-branding (R4)",
               "assumption"),
    "e_cap": (0.3, 0.9, "Design", "share of relocation blocked by a cap on discretionary channels (R13)",
              "assumption"),
}
NAMES = list(PRIORS)
GROUPS = []
for n in NAMES:
    g = PRIORS[n][2]
    if g not in GROUPS:
        GROUPS.append(g)

# fixed constants
CONST = {
    "quota": 37.2e6, "n_dep": 16, "phi_cur": 0.3, "d_e": 0.055, "d_tl": 0.074, "chi_cof": 0.3, "w_min": 0.02,
    "K": 6, "bonus_aligned": 1 / 3, "sup_safe": 0.55, "years_term": 4,
}

# designs: each a dict of switches; SQ / CL / L0 have no counties
BASE = dict(counties=True, conde=True, projects=True, closed_list=True, abolish=True, split="pc", college="count",
            approval="count",
            one_term=False, bar=True, territorial=True, contracts=False, cobrand=False, cofin=True,
            targets="absolute", technical=False, cap_disc=False, aligned_bonus=False, lrg=False)
DESIGNS = {
    "SQ": dict(BASE, counties=False, closed_list=False, abolish=False, bar=False, territorial=False),
    "CL": dict(BASE, counties=False, abolish=False, bar=False, territorial=False),
    "L0": dict(BASE, counties=False, closed_list=False, abolish=False, bar=False, territorial=False, lrg=True),
    "D0": dict(BASE, conde=False, projects=False, bar=False, territorial=False),
    "R0": dict(BASE),
    "R1": dict(BASE, one_term=True),
    "R2": dict(BASE, bar=False),
    "R3": dict(BASE, contracts=True),
    "R4": dict(BASE, cobrand=True),
    "R5": dict(BASE, cofin=False),
    "R6": dict(BASE, college="pop", approval="pop"),
    "R7": dict(BASE, approval="dual"),
    "R8": dict(BASE, targets="peers"),
    "R9": dict(BASE, territorial=False),
    "R10": dict(BASE, split="need"),
    "R11": dict(BASE, aligned_bonus=True),
    "R12": dict(BASE, technical=True),
    "R13": dict(BASE, cap_disc=True),
    "R14": dict(BASE, lrg=True),
    "R15": dict(BASE, contracts=True, cobrand=True, approval="dual", targets="peers", territorial=False, lrg=True),
    "R16": dict(BASE, contracts=True, cobrand=True, approval="dual", targets="peers", territorial=False, lrg=True,
                split="need"),
}
DESIGN_LABEL = {
    "SQ": "Status quo", "CL": "Closed lists only", "L0": "Status quo + managerial law",
    "D0": "Per-capita transfers, no counties", "R0": "Proposal as stated", "R1": "One-term conde", "R2": "No target bar on reappointment",
    "R3": "Binding consortium contracts", "R4": "Co-branding of projects", "R5": "No municipal co-financing",
    "R6": "Population-weighted college", "R7": "Dual majority for the plan", "R8": "Peer-relative targets",
    "R9": "Sanction on the conde only", "R10": "Need-based split", "R11": "Bonus to aligned condes",
    "R12": "Technical conde", "R13": "Cap on discretionary channels", "R14": "Proposal + managerial law",
    "R15": "Robust variant", "R16": "Robust variant + need-based split",
}


def lo_hi():
    lo = np.array([PRIORS[n][0] for n in NAMES])
    hi = np.array([PRIORS[n][1] for n in NAMES])
    return lo, hi


def from_unit(U):
    """Map points in the unit cube (rows) to parameter dicts of arrays."""
    lo, hi = lo_hi()
    X = lo + U * (hi - lo)
    return {n: X[:, i].copy() for i, n in enumerate(NAMES)}


def sample(n, seed=20261008):
    """Scrambled Sobol' sample of the priors (first n points)."""
    s = qmc.Sobol(d=len(NAMES), scramble=True, seed=seed)
    U = s.random_base2(int(np.ceil(np.log2(max(n, 2)))))[:n]
    return from_unit(U), U
