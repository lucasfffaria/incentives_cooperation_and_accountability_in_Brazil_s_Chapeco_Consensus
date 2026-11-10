/-
Proposition 5 (effort and crowding out), Supplementary Material 03, Section S3.5.

(i) Unmeasured effort is `e_u* = max{0, θ α_u Y/c_e - e_m}`, so every unit of measured effort
displaces one unit of unmeasured effort until none is left. (ii) With the proposal's bar, the
reappointment motive adds `V_R Pr(win) φ((μ(e_m) - z̄)/σ_z) μ'(e_m)/σ_z` to the marginal return of
measured effort; the motive is strongest for counties whose expected score is at the threshold and
vanishes for those far above or below it. (iii) With one vote per mayor, the probability of winning
depends on the average gain of the municipalities, each counting equally whatever its population.

In this file `a` stands for `θ α_u Y`, `ce` for `c_e`, `em` for `e_m` and `eu` for `e_u`. The
normal distribution function `Φ` is `Chapeco.normalCDF`, the distribution function of Mathlib's
standard Gaussian measure, and `φ` is `Chapeco.stdNormalPDF`.
-/
import ChapecoProofs.Basic

noncomputable section

open Real Filter Topology

namespace Chapeco.P5

/-! ## (i) Crowding out -/

/-- The part of the conde's objective that depends on unmeasured effort:
`θ α_u e_u Y - c_e (e_m + e_u)²/2`, with `a = θ α_u Y`. -/
def objective (a ce em eu : ℝ) : ℝ := a * eu - ce * (em + eu) ^ 2 / 2

/-- Unmeasured effort, `e_u* = max{0, a/c_e - e_m}`. -/
def unmeasuredEffort (a ce em : ℝ) : ℝ := max 0 (a / ce - em)

/-- **(i), Step 1.** `e_u*` maximizes the objective over `e_u ≥ 0`. -/
theorem objective_le {a ce em eu : ℝ} (hce : 0 < ce) (heu : 0 ≤ eu) :
    objective a ce em eu ≤ objective a ce em (unmeasuredEffort a ce em) := by
  obtain ⟨K, rfl⟩ : ∃ K, a = ce * K := ⟨a / ce, by field_simp⟩
  have hK : ce * K / ce = K := by field_simp
  unfold objective unmeasuredEffort
  rw [hK]
  rcases le_or_lt (K - em) 0 with h | h
  · rw [max_eq_left h]
    nlinarith [mul_nonneg (mul_nonneg hce.le heu) (by linarith : (0 : ℝ) ≤ em + eu / 2 - K)]
  · rw [max_eq_right h.le]
    nlinarith [mul_nonneg hce.le (sq_nonneg (K - em - eu))]

/-- **(i), Step 1 (uniqueness).** Any other `e_u ≥ 0` gives a strictly lower value. -/
theorem objective_lt {a ce em eu : ℝ} (hce : 0 < ce) (heu : 0 ≤ eu)
    (hne : eu ≠ unmeasuredEffort a ce em) :
    objective a ce em eu < objective a ce em (unmeasuredEffort a ce em) := by
  obtain ⟨K, rfl⟩ : ∃ K, a = ce * K := ⟨a / ce, by field_simp⟩
  have hK : ce * K / ce = K := by field_simp
  unfold objective
  unfold unmeasuredEffort at hne ⊢
  rw [hK] at hne ⊢
  rcases le_or_lt (K - em) 0 with h | h
  · rw [max_eq_left h] at hne ⊢
    have heu' : 0 < eu := lt_of_le_of_ne heu (Ne.symm hne)
    nlinarith [mul_pos (mul_pos hce heu') (by linarith : (0 : ℝ) < em + eu / 2 - K)]
  · rw [max_eq_right h.le] at hne ⊢
    have hsq : 0 < (K - em - eu) ^ 2 := by
      have : K - em - eu ≠ 0 := by
        intro h0
        exact hne (by linarith)
      positivity
    nlinarith [mul_pos hce hsq]

/-- **(i), Step 1.** Where `e_u* > 0`, measured and unmeasured effort add up to `a/c_e`. -/
theorem total_effort {a ce em : ℝ} (h : em ≤ a / ce) : em + unmeasuredEffort a ce em = a / ce := by
  unfold unmeasuredEffort
  rw [max_eq_right (by linarith)]
  ring

/-- **(i), Step 1.** Where `e_u* > 0`, `∂e_u*/∂e_m = -1`. -/
theorem hasDerivAt_unmeasuredEffort {a ce em : ℝ} (h : em < a / ce) :
    HasDerivAt (fun x => unmeasuredEffort a ce x) (-1) em := by
  have heq : (fun x => unmeasuredEffort a ce x) =ᶠ[𝓝 em] fun x => a / ce - x := by
    filter_upwards [gt_mem_nhds h] with x hx
    show unmeasuredEffort a ce x = a / ce - x
    unfold unmeasuredEffort
    rw [max_eq_right (by linarith)]
  exact ((hasDerivAt_id' em).const_sub (a / ce)).congr_of_eventuallyEq heq

/-! ## (ii) The reappointment motive -/

/-- **(ii), Step 2.** With the bar, the value of reappointment is
`V_R Pr(win) Φ((μ(e_m) - z̄)/σ_z)`; its derivative with respect to measured effort is
`V_R Pr(win) φ((μ(e_m) - z̄)/σ_z) μ'(e_m)/σ_z`. -/
theorem hasDerivAt_reappointment {VR Pwin zbar σ μ' e : ℝ} {μ : ℝ → ℝ} (hμ : HasDerivAt μ μ' e) :
    HasDerivAt (fun e => VR * (Pwin * normalCDF ((μ e - zbar) / σ)))
      (VR * Pwin * stdNormalPDF ((μ e - zbar) / σ) * μ' / σ) e := by
  have h1 : HasDerivAt (fun e => (μ e - zbar) / σ) (μ' / σ) e := (hμ.sub_const zbar).div_const σ
  have h2 := (hasDerivAt_normalCDF ((μ e - zbar) / σ)).comp e h1
  have h3 := (h2.const_mul Pwin).const_mul VR
  refine h3.congr_deriv ?_
  ring

/-- The density factor of the motive, as a function of the expected score `μ`. -/
def motiveFactor (zbar σ μ : ℝ) : ℝ := stdNormalPDF ((μ - zbar) / σ)

/-- **(ii).** The motive is strongest when the expected score is at the threshold. -/
theorem motiveFactor_le (zbar σ μ : ℝ) : motiveFactor zbar σ μ ≤ motiveFactor zbar σ zbar := by
  unfold motiveFactor
  rw [sub_self, zero_div]
  exact stdNormalPDF_le_zero _

/-- **(ii).** Strictly so for any other expected score. -/
theorem motiveFactor_lt {zbar σ μ : ℝ} (hσ : σ ≠ 0) (hμ : μ ≠ zbar) :
    motiveFactor zbar σ μ < motiveFactor zbar σ zbar := by
  unfold motiveFactor
  rw [sub_self, zero_div]
  exact stdNormalPDF_lt_zero (div_ne_zero (sub_ne_zero.2 hμ) hσ)

/-- **(ii).** The motive vanishes for counties far above the threshold. -/
theorem tendsto_motiveFactor_atTop {zbar σ : ℝ} (hσ : 0 < σ) :
    Tendsto (motiveFactor zbar σ) atTop (𝓝 0) := by
  have h : Tendsto (fun μ : ℝ => (μ - zbar) / σ) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b * σ + zbar, fun x hx => by
      show b ≤ (x - zbar) / σ
      rw [le_div_iff₀ hσ]
      linarith⟩
  exact tendsto_stdNormalPDF_atTop.comp h

/-- **(ii).** The motive vanishes for counties far below the threshold. -/
theorem tendsto_motiveFactor_atBot {zbar σ : ℝ} (hσ : 0 < σ) :
    Tendsto (motiveFactor zbar σ) atBot (𝓝 0) := by
  have h : Tendsto (fun μ : ℝ => (μ - zbar) / σ) atBot atBot :=
    tendsto_atBot_atBot.2 fun b => ⟨b * σ + zbar, fun x hx => by
      show (x - zbar) / σ ≤ b
      rw [div_le_iff₀ hσ]
      linarith⟩
  exact tendsto_stdNormalPDF_atBot.comp h

/-! ## (iii) One vote per mayor -/

/-- **(iii), Step 3.** With one vote per mayor, each of the `n` mayors has weight `1/n`, so the
quantity that determines the probability of winning is the mean of the mayors' gains; the
municipalities' populations do not enter. -/
def oneVoteMean {ι : Type*} (s : Finset ι) (gain : ι → ℝ) : ℝ :=
  ∑ m ∈ s, (1 / (s.card : ℝ)) * gain m

theorem oneVoteMean_eq {ι : Type*} (s : Finset ι) (gain : ι → ℝ) :
    oneVoteMean s gain = (∑ m ∈ s, gain m) / s.card := by
  unfold oneVoteMean
  rw [← Finset.mul_sum]
  ring

end Chapeco.P5
