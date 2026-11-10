# -*- coding: utf-8 -*-
"""Federal-deputy votes in Santa Catarina, 2022 and 2026, by candidate and municipality, from the official TSE files
"votacao_candidato_munzona_<year>_SC.csv" (Repositório de Dados Eleitorais, TSE), supplied by the author.

Inputs  data/raw_tse/votacao_candidato_munzona_2022_SC.csv, ..._2026_SC.csv  (not redistributed; 225 MB)
        data/companion/sc_mayors_panel_2016_2024.csv                        (TSE -> IBGE municipal codes)
Outputs data/derived/tse_fed_2022.csv, tse_fed_2026.csv                     (candidate x municipality votes)
        data/derived/tse_summary.json                                        (seats, re-election, checks)
If the raw files are absent, the derived files shipped with the package are used as they are.
"""
import os, json, unicodedata
import numpy as np, pandas as pd

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RAW = os.path.join(ROOT, "data", "raw_tse")
DER = os.path.join(ROOT, "data", "derived")
C = os.path.join(ROOT, "data", "companion")

# the 16 deputies elected in 2022, as named in the 2025 special-transfer data, and their TSE ballot names
PIX_TO_TSE = {"Carmen Zanotto": "CARMEN ZANOTTO", "Caroline de Toni": "CAROL DE TONI", "Jorge Goetten": "JORGE GOETTEN",
              "Julia Zanatta": "JULIA ZANATTA", "Daniel Freitas": "DANIEL FREITAS", "Daniela Reinehr": "DANIELA REINEHR",
              "Zé Trovão": "ZÉ TROVÃO", "Fabio Schiochet": "FABIO SCHIOCHET", "Pedro Uczai": "PROFESSOR PEDRO UCZAI",
              "Ana Paula Lima": "ANA PAULA LIMA", "Cobalchini": "COBALCHINI", "Carlos Chiodini": "CARLOS CHIODINI",
              "Pezenti": "RAFAEL PEZENTI", "Ismael": "ISMAEL", "Ricardo Guidi": "RICARDO GUIDI",
              "Gilson Marques": "GILSON MARQUES"}


def norm(s):
    s = unicodedata.normalize("NFKD", str(s)).encode("ascii", "ignore").decode()
    return " ".join(s.upper().split())


def crosswalk():
    pan = pd.read_csv(os.path.join(C, "sc_mayors_panel_2016_2024.csv"))
    cw = dict(zip(pan.cd_municipio_tse, pan.cd_municipio_ibge))
    cw.update({81507: 4215687, 81205: 4215695})   # swapped codes in the companion files (see prep_data2.py)
    assert len(set(cw.values())) == 295
    return cw


def load(year, cw):
    f = os.path.join(RAW, f"votacao_candidato_munzona_{year}_SC.csv")
    df = pd.read_csv(f, sep=";", encoding="latin1", low_memory=False)
    df = df[(df.CD_CARGO == 6) & (df.NR_TURNO == 1)]
    df["ibge_id"] = df.CD_MUNICIPIO.map(cw)
    assert df.ibge_id.notna().all()
    g = df.groupby(["ibge_id", "SQ_CANDIDATO", "NM_CANDIDATO", "NM_URNA_CANDIDATO", "SG_PARTIDO", "SG_FEDERACAO",
                    "DS_SIT_TOT_TURNO", "NM_TIPO_DESTINACAO_VOTOS"], dropna=False)
    out = g[["QT_VOTOS_NOMINAIS", "QT_VOTOS_NOMINAIS_VALIDOS"]].sum().reset_index()
    out.columns = ["ibge_id", "cand_id", "name", "ballot_name", "party", "federation", "status", "destination",
                   "votes", "votes_valid"]
    out["elected"] = out.status.str.startswith("ELEITO").astype(int)
    out["ibge_id"] = out.ibge_id.astype(int)
    return out


def main():
    os.makedirs(DER, exist_ok=True)
    if not os.path.exists(os.path.join(RAW, "votacao_candidato_munzona_2022_SC.csv")):
        print("raw TSE files absent: using the derived files shipped with the package")
        return
    cw = crosswalk()
    v22, v26 = load(2022, cw), load(2026, cw)
    v22.to_csv(os.path.join(DER, "tse_fed_2022.csv"), index=False)
    v26.to_csv(os.path.join(DER, "tse_fed_2026.csv"), index=False)
    S = {}
    for y, v in ((2022, v22), (2026, v26)):
        el = v[v.elected == 1].groupby(["name", "ballot_name", "party", "federation"])["votes"].sum().reset_index()
        assert len(el) == 16, (y, len(el))
        S[f"seats_{y}"] = el.party.value_counts().to_dict()
        S[f"nominal_votes_{y}"] = int(v.votes.sum())
        S[f"valid_nominal_votes_{y}"] = int(v.votes_valid.sum())
        S[f"party_nominal_share_{y}"] = (v.groupby("party").votes_valid.sum() / v.votes_valid.sum()).round(4) \
            .sort_values(ascending=False).head(15).to_dict()
        S[f"n_candidates_{y}"] = int(v.cand_id.nunique())
    # the 2022 deputies (Pix authors) in 2026
    n22 = v22[v22.elected == 1].groupby(["name", "ballot_name", "party"]).votes.sum().reset_index()
    n26 = v26.groupby(["name", "ballot_name", "party", "elected"]).votes.sum().reset_index()
    n26["key"] = n26.name.map(norm)
    rows = []
    for pix, ballot in PIX_TO_TSE.items():
        r = n22[n22.ballot_name == ballot]
        assert len(r) == 1, ballot
        key = norm(r.name.iloc[0])
        r6 = n26[n26.key == key]
        rows.append({"pix_name": pix, "ballot_2022": ballot, "party_2022": r.party.iloc[0],
                     "votes_2022": int(r.votes.iloc[0]), "ran_2026": int(len(r6) > 0),
                     "party_2026": r6.party.iloc[0] if len(r6) else None,
                     "votes_2026": int(r6.votes.sum()) if len(r6) else 0,
                     "elected_2026": int(r6.elected.max()) if len(r6) else 0})
    S["deputies_2022"] = rows
    S["n_ran_2026"] = int(sum(r["ran_2026"] for r in rows))
    S["n_reelected_2026"] = int(sum(r["elected_2026"] for r in rows))
    S["n_switched_party"] = int(sum(1 for r in rows if r["ran_2026"] and r["party_2026"] != r["party_2022"]))
    json.dump(S, open(os.path.join(DER, "tse_summary.json"), "w"), indent=1, ensure_ascii=False)
    for k, v in S.items():
        if k != "deputies_2022":
            print(k, v)
    for r in rows:
        print(r)


if __name__ == "__main__":
    main()
