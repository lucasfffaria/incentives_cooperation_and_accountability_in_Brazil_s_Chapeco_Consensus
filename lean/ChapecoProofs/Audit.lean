/-
Audit of the formalization: checks that no declaration of the `Chapeco` namespace depends on
`sorry` or on any axiom other than the three standard axioms of Lean and Mathlib (`propext`,
`Classical.choice`, `Quot.sound`). The build fails if the check fails.
-/
import ChapecoProofs.P1Selection
import ChapecoProofs.P2Effort
import ChapecoProofs.P3Cooperation
import ChapecoProofs.P4Hurdle
import ChapecoProofs.P5CrowdingOut
import ChapecoProofs.P6Tilt
import ChapecoProofs.P7SanctionTrap
import ChapecoProofs.SP8Sanctions
import ChapecoProofs.SP9Inspection

open Lean Elab Command

/-- Checks every declaration of the `Chapeco` namespace for `sorry` and nonstandard axioms. -/
elab "#audit_chapeco" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let names := env.constants.fold
    (fun acc n _ => if (`Chapeco).isPrefixOf n && !n.isInternal then n :: acc else acc) []
  for n in names do
    let axs ← collectAxioms n
    for a in axs do
      unless allowed.contains a do
        throwError "{n} depends on {a}"
  logInfo m!"{names.length} declarations in the Chapeco namespace checked: none uses sorry, \
    and none depends on an axiom other than propext, Classical.choice and Quot.sound."

#audit_chapeco

/-! Axioms used by the main statement of each proposition. -/

#print axioms Chapeco.P1.expected_mean_skill_elected
#print axioms Chapeco.P1.corr_strictAntiOn
#print axioms Chapeco.P2.proposition2_effort
#print axioms Chapeco.P2.legislative_effort_rises_iff
#print axioms Chapeco.P3.proposition3
#print axioms Chapeco.P3.completionGain_taylor
#print axioms Chapeco.P4.include_iff_hurdle
#print axioms Chapeco.P4.hurdle_deriv_neg_iff
#print axioms Chapeco.P5.objective_le
#print axioms Chapeco.P5.hasDerivAt_reappointment
#print axioms Chapeco.P6.total_tiltGain_le
#print axioms Chapeco.P6.hasDerivAt_winProb
#print axioms Chapeco.P7.bar_lowers_map_normal
#print axioms Chapeco.P7.sanction_trap
#print axioms Chapeco.SP8.supplementary_proposition8
#print axioms Chapeco.SP9.supplementary_proposition9
