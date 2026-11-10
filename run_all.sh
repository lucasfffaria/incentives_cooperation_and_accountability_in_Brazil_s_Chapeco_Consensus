#!/bin/sh
# Rebuild every output, figure and table of the article and its Supplementary Material.
# Requirements: Python 3.11+ with numpy, scipy, pandas, statsmodels, scikit-learn, matplotlib, geopandas (maps).
# Runtime on the test machine used for the study: about 20 minutes.
set -e
cd "$(dirname "$0")/code"
mkdir -p ../out/tables ../figs
t0=$(date +%s)
step() { echo "== $1 ($(( $(date +%s) - t0 ))s)"; }
step "data";            python3 prep_tse.py > ../out/prep_tse.log
                        python3 prep_data2.py > ../out/prep_data2.log
                        python3 electoral_connection.py > ../out/electoral_connection.log
                        python3 pix_impediments.py > ../out/pix_impediments.log
                        python3 college_expected.py > ../out/college_expected.log
                        python3 real_colleges.py > ../out/real_colleges.log
                        python3 national_accounting.py > ../out/national_accounting.log
step "engine tests";    python3 cc2_tests_engine.py | tee ../out/cc2_tests_engine.log | tail -1
step "propositions";    python3 cc2_props.py > ../out/cc2_props.log
step "experiment";      python3 cc2_run.py 2000 > ../out/cc2_run.log
step "mechanisms";      python3 cc2_mech.py > ../out/cc2_mech.log
step "analysis";        python3 cc2_analyze.py > ../out/cc2_analyze.log
                        python3 cc2_textnums.py > ../out/cc2_textnums.log
step "robustness";      python3 cc2_robust.py > ../out/cc2_robust.log
step "sensitivity R0";  python3 cc2_gsa.py 1024 10 R0 > ../out/cc2_gsa_R0.log 2>&1
step "sensitivity R15"; python3 cc2_gsa.py 1024 10 R15 > ../out/cc2_gsa_R15.log 2>&1
step "figures"
for f in fig_c1_maps fig_c2_cycle fig_c3_statusquo fig_c4_chamber fig_c5_control fig_c6_coop fig_c7_value \
         fig_c8_sanctions fig_c9_designs fig_c10_discovery fig_c11_national fig_s_supp fig_s_electoral; do
  python3 $f.py > /dev/null
done
step "tables";          python3 cc2_tables.py > /dev/null
step "done"
