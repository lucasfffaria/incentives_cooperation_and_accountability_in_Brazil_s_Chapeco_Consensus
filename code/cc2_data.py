# -*- coding: utf-8 -*-
"""Geography, parties and the real status quo, loaded once for the model."""
import os, json
import numpy as np, pandas as pd

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DER = os.path.join(ROOT, "data", "derived")

PARTIES = ["PL", "MDB", "PP", "PSD", "PSDB", "UNIÃO", "PT", "REPUBLICANOS", "NOVO", "PODEMOS", "CIDADANIA", "OTHER"]
PIDX = {p: i for i, p in enumerate(PARTIES)}
SEATS_2022 = {"PL": 6, "MDB": 3, "PT": 2, "PSD": 2, "UNIÃO": 1, "NOVO": 1, "CIDADANIA": 1}
# the 16 deputies elected in October 2026 (TSE; prep_tse.py), who would sit in 2027-2030; a federation's seats are given
# to its main party, because a federation would present a single closed list (PT/PCdoB/PV: 2 PT + 1 PCdoB; UNIÃO/PP: 1 PP)
SEATS_2026 = {"PL": 7, "PT": 3, "MDB": 1, "NOVO": 1, "PSD": 1, "PP": 1, "PODEMOS": 1, "REPUBLICANOS": 1}
SEATS = SEATS_2026


class Geo:
    def __init__(self, sq_variant="main", counties="health"):
        m = pd.read_csv(os.path.join(DER, "sc_master2.csv"))
        self.df = m
        self.M = len(m)
        self.ibge = m.ibge_id.values
        self.name = m.municipality.values
        self.pop = m.pop2022.values.astype(float)
        self.need = m.need.values
        self.kappa = m.kappa.values
        self.kbar = self.kappa.mean()
        self.rev = m.rev_pc.values * self.pop                      # current revenue, R$ per year (2024)
        self.gdp_pc = m.gdp_pc_2021.values
        self.x = m.x_km.values;
        self.y = m.y_km.values
        self.dist = np.hypot(self.x[:, None] - self.x[None, :], self.y[:, None] - self.y[None, :])
        self.party0 = np.array([PIDX.get(p, PIDX["OTHER"]) for p in m.party.values])
        self.tl0 = m.term_limited_2025_28.values.astype(bool)     # term-limited in 2025-28
        self.size_class = m.size_class.values
        col = "health_region_2024" if counties == "health" else "macro_region_2024"
        regs = sorted(m[col].unique(), key=lambda r: m.loc[m[col] == r, "x_km"].mean())
        self.regions = regs
        self.J = len(regs)
        self.cty = np.array([regs.index(r) for r in m[col].values])
        self.members = [np.where(self.cty == j)[0] for j in range(self.J)]
        self.n_j = np.array([len(i) for i in self.members])
        self.pop_j = np.array([self.pop[i].sum() for i in self.members])
        self.polo = np.array([i[np.argmax(self.pop[i])] for i in self.members])
        self.kappa_j = np.array([np.average(self.kappa[i], weights=self.pop[i]) for i in self.members])
        self.need_j = np.array([np.average(self.need[i], weights=self.pop[i]) for i in self.members])
        gdp_j = np.array([self.gdp_pc[i] @ self.pop[i] / self.pop[i].sum() for i in self.members])
        lg = np.log(gdp_j)
        self.cap_j = (lg - lg.mean()) / lg.std()                  # county capacity in the score (standardized)
        self.cap_terc = np.digitize(self.cap_j, np.quantile(self.cap_j, [1 / 3, 2 / 3]))
        a = np.load(os.path.join(DER, "sq_alloc.npz"), allow_pickle=True)
        self.sq_dm = a[sq_variant]                                 # deputy x municipality, R$ per year
        self.x_sq = self.sq_dm.sum(0)
        self.dep_party = np.array([PIDX[p] for p in a["dep_party"]])
        self.M_tot = self.x_sq.sum()
        st = json.load(open(os.path.join(DER, "data_stats.json")))
        sh = st["mayors"]["party_shares_2024"]
        s = np.zeros(len(PARTIES))
        for p, v in sh.items():
            s[PIDX.get("PODEMOS" if p == "PODE" else p, PIDX["OTHER"])] += v
        s[PIDX["OTHER"]] = max(s[PIDX["OTHER"]], 0.01)            # room for parties without mayors in 2024
        self.state_share0 = s / s.sum()
        # mean of the statewide climate for seats that change hands. A seat that changes hands goes to another party,
        # so a climate equal to the current shares would shrink large parties and grow small ones; the weights w solve
        # w_p * sum_{q != p} c_q / (1 - w_q) = c_p, which keeps the expected party composition at its 2024 level
        c = self.state_share0
        w = c.copy()
        for _ in range(500):
            S = np.array([(c / (1 - w)).sum() - c[p] / (1 - w[p]) for p in range(len(c))])
            w_new = c / S
            w_new = w_new / w_new.sum()
            if np.max(np.abs(w_new - w)) < 1e-13:
                w = w_new
                break
            w = w_new
        self.climate0 = w
        self.P = len(PARTIES)
        self.seats = np.array([SEATS.get(p, 0) for p in PARTIES])
