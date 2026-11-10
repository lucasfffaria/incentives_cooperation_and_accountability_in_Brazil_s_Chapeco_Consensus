/-
Proposition 6 (pre-election tilt), Supplementary Material 03, Section S3.6.

With electoral returns that diminish in the money received, the conde's tilt toward co-partisan
municipality `m` is `T_m = (A_m/λ - h_V Rev_m)⁺`, and, at the margin, raising the expected number
of co-partisan mayors by one costs `Rev_m/[p_m (1 - p_m) α_V]`.

The conde maximizes the linearized gain `∑_m A_m ln(1 + T_m/(h_V Rev_m)) - λ ∑_m T_m` over
`T_m ≥ 0` (Step 2 of the proof defines this objective by linearizing `Λ` around the status quo).
In this file `c` stands for `h_V Rev_m > 0` and `lam` for `λ`.

What is formalized here: the water-filling solution is the unique optimum, municipality by
municipality and for the sum (`tiltGain_le`, `tiltGain_lt`, `total_tiltGain_le`); the Kuhn–Tucker
condition (`kkt`); and the derivative of the probability of winning at `T = 0` and the price of
control (`hasDerivAt_winProb`, `price_of_control`).
-/
import ChapecoProofs.Basic

noncomputable section

open Real Filter Topology

namespace Chapeco.P6

/-- The gain from tilting `T` toward a municipality, net of its cost: `A ln(1 + T/c) - λ T`. -/
def tiltGain (A c lam T : ℝ) : ℝ := A * Real.log (1 + T / c) - lam * T

/-- The water-filling tilt `(A/λ - c)⁺`. -/
def waterFilling (A c lam : ℝ) : ℝ := max 0 (A / lam - c)

theorem waterFilling_nonneg (A c lam : ℝ) : 0 ≤ waterFilling A c lam := le_max_left _ _

/-- **Step 3.** The water-filling tilt maximizes the net gain over `T ≥ 0`. -/
theorem tiltGain_le {A c lam : ℝ} (hA : 0 < A) (hc : 0 < c) (hlam : 0 < lam) {T : ℝ}
    (hT : 0 ≤ T) : tiltGain A c lam T ≤ tiltGain A c lam (waterFilling A c lam) := by
  have hu : 0 < 1 + T / c := by positivity
  unfold tiltGain waterFilling
  rcases le_or_lt (A / lam - c) 0 with h | h
  · rw [max_eq_left h]
    simp only [zero_div, add_zero, Real.log_one, mul_zero, sub_zero]
    have hlog : Real.log (1 + T / c) ≤ T / c := by
      have := Real.log_le_sub_one_of_pos hu
      linarith
    have hAc : A / c ≤ lam := by
      rw [div_le_iff₀ hc]
      rw [sub_nonpos, div_le_iff₀ hlam] at h
      linarith
    have h1 : A * Real.log (1 + T / c) ≤ A * (T / c) := mul_le_mul_of_nonneg_left hlog hA.le
    have h2 : A * (T / c) = T * (A / c) := by ring
    have h3 : T * (A / c) ≤ T * lam := mul_le_mul_of_nonneg_left hAc hT
    linarith
  · rw [max_eq_right h.le]
    have hus : 0 < 1 + (A / lam - c) / c := by
      have : 0 < (A / lam - c) / c := div_pos h hc
      linarith
    have hlog : Real.log (1 + T / c) - Real.log (1 + (A / lam - c) / c) ≤
        (1 + T / c) / (1 + (A / lam - c) / c) - 1 := by
      rw [← Real.log_div hu.ne' hus.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hu hus)
    have hA' : A ≠ 0 := hA.ne'
    have hc' : c ≠ 0 := hc.ne'
    have hlam' : lam ≠ 0 := hlam.ne'
    have hratio : (1 + T / c) / (1 + (A / lam - c) / c) = lam * (c + T) / A := by
      rw [div_eq_div_iff hus.ne' hA']
      field_simp
      ring
    rw [hratio] at hlog
    have h1 := mul_le_mul_of_nonneg_left hlog hA.le
    have h2 : A * (lam * (c + T) / A - 1) = lam * (c + T) - A := by
      field_simp
    have h3 : lam * (A / lam - c) = A - lam * c := by
      field_simp
    rw [h2] at h1
    nlinarith

/-- **Step 3 (uniqueness).** Any other `T ≥ 0` gives a strictly lower net gain. -/
theorem tiltGain_lt {A c lam : ℝ} (hA : 0 < A) (hc : 0 < c) (hlam : 0 < lam) {T : ℝ}
    (hT : 0 ≤ T) (hne : T ≠ waterFilling A c lam) :
    tiltGain A c lam T < tiltGain A c lam (waterFilling A c lam) := by
  have hu : 0 < 1 + T / c := by positivity
  unfold waterFilling at hne
  unfold tiltGain waterFilling
  rcases le_or_lt (A / lam - c) 0 with h | h
  · rw [max_eq_left h] at hne ⊢
    simp only [zero_div, add_zero, Real.log_one, mul_zero, sub_zero]
    have hT' : 0 < T := lt_of_le_of_ne hT (Ne.symm hne)
    have hne1 : 1 + T / c ≠ 1 := by
      have : 0 < T / c := div_pos hT' hc
      linarith
    have hlog : Real.log (1 + T / c) < T / c := by
      have := Real.log_lt_sub_one_of_pos hu hne1
      linarith
    have hAc : A / c ≤ lam := by
      rw [div_le_iff₀ hc]
      rw [sub_nonpos, div_le_iff₀ hlam] at h
      linarith
    have h1 : A * Real.log (1 + T / c) < A * (T / c) := mul_lt_mul_of_pos_left hlog hA
    have h2 : A * (T / c) = T * (A / c) := by ring
    have h3 : T * (A / c) ≤ T * lam := mul_le_mul_of_nonneg_left hAc hT
    linarith
  · rw [max_eq_right h.le] at hne ⊢
    have hus : 0 < 1 + (A / lam - c) / c := by
      have : 0 < (A / lam - c) / c := div_pos h hc
      linarith
    have hA' : A ≠ 0 := hA.ne'
    have hc' : c ≠ 0 := hc.ne'
    have hlam' : lam ≠ 0 := hlam.ne'
    have hratio : (1 + T / c) / (1 + (A / lam - c) / c) = lam * (c + T) / A := by
      rw [div_eq_div_iff hus.ne' hA']
      field_simp
      ring
    have hne1 : (1 + T / c) / (1 + (A / lam - c) / c) ≠ 1 := by
      rw [hratio]
      intro h1
      rw [div_eq_one_iff_eq hA'] at h1
      apply hne
      field_simp
      linarith
    have hlog : Real.log (1 + T / c) - Real.log (1 + (A / lam - c) / c) <
        (1 + T / c) / (1 + (A / lam - c) / c) - 1 := by
      rw [← Real.log_div hu.ne' hus.ne']
      exact Real.log_lt_sub_one_of_pos (div_pos hu hus) hne1
    rw [hratio] at hlog
    have h1 := mul_lt_mul_of_pos_left hlog hA
    have h2 : A * (lam * (c + T) / A - 1) = lam * (c + T) - A := by
      field_simp
    have h3 : lam * (A / lam - c) = A - lam * c := by
      field_simp
    rw [h2] at h1
    nlinarith

/-- **Proposition 6.** The water-filling tilts maximize the conde's objective
`∑_m [A_m ln(1 + T_m/c_m) - λ T_m]` over all tilts `T_m ≥ 0`. -/
theorem total_tiltGain_le {ι : Type*} (s : Finset ι) {A c : ι → ℝ} {lam : ℝ}
    (hA : ∀ m, 0 < A m) (hc : ∀ m, 0 < c m) (hlam : 0 < lam) {T : ι → ℝ} (hT : ∀ m, 0 ≤ T m) :
    ∑ m ∈ s, tiltGain (A m) (c m) lam (T m) ≤
      ∑ m ∈ s, tiltGain (A m) (c m) lam (waterFilling (A m) (c m) lam) :=
  Finset.sum_le_sum fun m _ => tiltGain_le (hA m) (hc m) hlam (hT m)

/-- **Step 3 (Kuhn–Tucker).** Where the tilt is positive, `A/(c + T) = λ`. -/
theorem kkt {A c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hpos : 0 < waterFilling A c lam) :
    A / (c + waterFilling A c lam) = lam := by
  unfold waterFilling at hpos ⊢
  have h : 0 < A / lam - c := (lt_max_iff.1 hpos).resolve_left (lt_irrefl 0)
  rw [max_eq_right h.le]
  have hAl : 0 < A / lam := by linarith
  have hA : A ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hAl
    exact lt_irrefl 0 hAl
  have hlam' : lam ≠ 0 := hlam.ne'
  rw [show c + (A / lam - c) = A / lam by ring, div_div_eq_mul_div, mul_div_cancel_left₀ _ hA]

/-! ## Step 4: the price of control -/

/-- Diminishing electoral returns, `g(x) = h_V ln(1 + x/h_V)`. -/
def gReturn (hV x : ℝ) : ℝ := hV * Real.log (1 + x / hV)

/-- The probability that the conde's party keeps or wins the municipality,
`p(T) = Λ(a + α_V g(T/Rev))`. -/
def winProb (a αV hV Rev T : ℝ) : ℝ := logistic (a + αV * gReturn hV (T / Rev))

/-- **Step 4.** At `T = 0`, `∂p/∂T = p (1 - p) α_V/Rev`, because `g'(0) = 1`. -/
theorem hasDerivAt_winProb {a αV hV Rev : ℝ} (hh : 0 < hV) (hRev : 0 < Rev) :
    HasDerivAt (winProb a αV hV Rev) (logistic a * (1 - logistic a) * αV / Rev) 0 := by
  have h1 : HasDerivAt (fun T => 1 + T / Rev / hV) (1 / Rev / hV) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).div_const Rev).div_const hV).const_add 1
  have h2 : HasDerivAt (fun T => Real.log (1 + T / Rev / hV)) (1 / Rev / hV / (1 + 0 / Rev / hV))
      0 := h1.log (by simp)
  have h3 : HasDerivAt (fun T => a + αV * (hV * Real.log (1 + T / Rev / hV)))
      (αV * (hV * (1 / Rev / hV / (1 + 0 / Rev / hV)))) 0 :=
    ((h2.const_mul hV).const_mul αV).const_add a
  have hpt : a + αV * (hV * Real.log (1 + 0 / Rev / hV)) = a := by simp
  have h4 := (hasDerivAt_logistic (a + αV * (hV * Real.log (1 + 0 / Rev / hV)))).comp 0 h3
  rw [hpt] at h4
  show HasDerivAt (fun T => logistic (a + αV * (hV * Real.log (1 + T / Rev / hV)))) _ 0
  refine h4.congr_deriv ?_
  have hh' : hV ≠ 0 := hh.ne'
  have hR' : Rev ≠ 0 := hRev.ne'
  simp only [zero_div, add_zero]
  field_simp
  ring

/-- **Step 4.** Raising `p` by one unit costs `Rev/[p (1 - p) α_V]`, the reciprocal of the
derivative. -/
theorem price_of_control (p αV Rev : ℝ) :
    (p * (1 - p) * αV / Rev)⁻¹ = Rev / (p * (1 - p) * αV) :=
  inv_div _ _

end Chapeco.P6
