/-
Supplementary Proposition 9 (inspection), Supplementary Material 03, Section S3.9.

Each real of potential diversion is attempted if its expected return exceeds a private cost
`c ~ U[0,1]`; inspection detects and blocks a share `p_I` of attempts, and a detected attempt pays
a penalty `s_D` per real. Then diversion is multiplied by `I = (1 - p_I)[1 - p_I(1 + s_D)]⁺`, and
without inspection (`p_I = 0`) the factor is one.

The uniform distribution is Mathlib's `MeasureTheory.pdf.IsUniform` with respect to Lebesgue
measure.
-/
import ChapecoProofs.Basic

noncomputable section

open Real MeasureTheory

namespace Chapeco.SP9

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- For `C` uniform on `[0, 1]` and `x ≤ 1`, `Pr(C < x) = x⁺`. -/
theorem prob_lt {C : Ω → ℝ} {x : ℝ} (hx : x ≤ 1) (hU : pdf.IsUniform C (Set.Icc 0 1) P) :
    P {ω | C ω < x} = ENNReal.ofReal x := by
  have hvol : volume (Set.Icc (0 : ℝ) 1) = 1 := by
    rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
  have hns : volume (Set.Icc (0 : ℝ) 1) ≠ 0 := by
    rw [hvol]
    exact one_ne_zero
  have hnt : volume (Set.Icc (0 : ℝ) 1) ≠ ⊤ := by
    rw [hvol]
    exact ENNReal.one_ne_top
  have h := hU.measure_preimage hns hnt (measurableSet_Iio : MeasurableSet (Set.Iio x))
  have hpre : {ω | C ω < x} = C ⁻¹' Set.Iio x := rfl
  rw [hpre, h, hvol, div_one]
  rcases le_or_lt x 0 with h0 | h0
  · have he : Set.Icc (0 : ℝ) 1 ∩ Set.Iio x = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨hy0, _⟩, hyx⟩
      linarith
    rw [he, measure_empty, eq_comm, ENNReal.ofReal_eq_zero]
    exact h0
  · have he : Set.Icc (0 : ℝ) 1 ∩ Set.Iio x = Set.Ico 0 x := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, by linarith⟩, h2⟩
    rw [he, Real.volume_Ico, sub_zero]

/-- The factor by which inspection multiplies diversion. -/
def inspectionFactor (p s : ℝ) : ℝ := (1 - p) * max (1 - p * (1 + s)) 0

/-- The expected return of an attempt: one real with probability `1 - p_I`, a penalty `s_D` with
probability `p_I`. -/
theorem expected_return (p s : ℝ) : (1 - p) * 1 + p * (-s) = 1 - p * (1 + s) := by
  ring

/-- **Supplementary Proposition 9.** The share of potential diversion attempted is
`Pr(c < 1 - p_I(1 + s_D)) = [1 - p_I(1 + s_D)]⁺`; a share `1 - p_I` of attempts succeeds. -/
theorem supplementary_proposition9 {C : Ω → ℝ} {p s : ℝ} (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hU : pdf.IsUniform C (Set.Icc 0 1) P) :
    (1 - p) * P.real {ω | C ω < 1 - p * (1 + s)} = inspectionFactor p s := by
  have hx : 1 - p * (1 + s) ≤ 1 := by nlinarith
  rw [measureReal_def, prob_lt hx hU, ENNReal.toReal_ofReal']
  rfl

/-- Without inspection, the factor is one. -/
theorem inspectionFactor_zero (s : ℝ) : inspectionFactor 0 s = 1 := by
  unfold inspectionFactor
  rw [max_eq_left (by norm_num)]
  ring

end Chapeco.SP9
