/-
Supplementary Proposition 8 (credibility of territorial sanctions), Supplementary Material 03,
Section S3.8.

If the Union's private benefit from enforcing a cut on a failing county is uniform on `[0, Ξ]`, and
the political cost of enforcing it is `n^ϱ`, where `n` is the county's need, the cut is enforced
with probability `Φ = (1 - n^ϱ/Ξ)⁺`, which falls with need when `ϱ > 0`.

The uniform distribution is Mathlib's `MeasureTheory.pdf.IsUniform` with respect to Lebesgue
measure.
-/
import ChapecoProofs.Basic

noncomputable section

open Real MeasureTheory

namespace Chapeco.SP8

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem volume_Icc_zero (Ξ : ℝ) : volume (Set.Icc (0 : ℝ) Ξ) = ENNReal.ofReal Ξ := by
  rw [Real.volume_Icc, sub_zero]

/-- For `U` uniform on `[0, Ξ]` and `0 ≤ k`, `Pr(U > k) = (1 - k/Ξ)⁺`. -/
theorem prob_gt {U : Ω → ℝ} {Ξ k : ℝ} (hΞ : 0 < Ξ) (hk : 0 ≤ k)
    (hU : pdf.IsUniform U (Set.Icc 0 Ξ) P) :
    P {ω | k < U ω} = ENNReal.ofReal (1 - k / Ξ) := by
  have hvol := volume_Icc_zero Ξ
  have hns : volume (Set.Icc (0 : ℝ) Ξ) ≠ 0 := by
    rw [hvol, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hΞ
  have hnt : volume (Set.Icc (0 : ℝ) Ξ) ≠ ⊤ := by
    rw [hvol]
    exact ENNReal.ofReal_ne_top
  have h := hU.measure_preimage hns hnt (measurableSet_Ioi : MeasurableSet (Set.Ioi k))
  have hpre : {ω | k < U ω} = U ⁻¹' Set.Ioi k := rfl
  rw [hpre, h, hvol]
  rcases le_or_lt Ξ k with hkΞ | hkΞ
  · have he : Set.Icc (0 : ℝ) Ξ ∩ Set.Ioi k = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, hy⟩, hky⟩
      linarith
    rw [he, measure_empty, ENNReal.zero_div, eq_comm, ENNReal.ofReal_eq_zero, sub_nonpos,
      le_div_iff₀ hΞ]
    linarith
  · have he : Set.Icc (0 : ℝ) Ξ ∩ Set.Ioi k = Set.Ioc k Ξ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by linarith, h2⟩, h1⟩
    rw [he, Real.volume_Ioc, ← ENNReal.ofReal_div_of_pos hΞ, sub_div, div_self hΞ.ne']

/-- The probability of enforcement, `Φ = (1 - n^ϱ/Ξ)⁺`. -/
def enforceProb (Ξ ϱ n : ℝ) : ℝ := max (1 - n ^ ϱ / Ξ) 0

/-- **Supplementary Proposition 8.** The Union enforces the cut, which it does if and only if its
benefit `U` exceeds the cost `n^ϱ`, with probability `(1 - n^ϱ/Ξ)⁺`. -/
theorem supplementary_proposition8 {U : Ω → ℝ} {Ξ ϱ n : ℝ} (hΞ : 0 < Ξ) (hn : 0 ≤ n)
    (hU : pdf.IsUniform U (Set.Icc 0 Ξ) P) :
    P.real {ω | n ^ ϱ < U ω} = enforceProb Ξ ϱ n := by
  rw [measureReal_def, prob_gt hΞ (Real.rpow_nonneg hn ϱ) hU, ENNReal.toReal_ofReal']
  rfl

/-- The probability of enforcement falls with need when `ϱ > 0`. -/
theorem enforceProb_antitoneOn {Ξ ϱ : ℝ} (hΞ : 0 < Ξ) (hϱ : 0 < ϱ) :
    AntitoneOn (enforceProb Ξ ϱ) (Set.Ici 0) := by
  intro a ha b hb hab
  unfold enforceProb
  apply max_le_max _ le_rfl
  have h1 : a ^ ϱ ≤ b ^ ϱ := Real.rpow_le_rpow ha hab hϱ.le
  have h2 : a ^ ϱ / Ξ ≤ b ^ ϱ / Ξ := div_le_div_of_nonneg_right h1 hΞ.le
  linarith

/-- Strictly so where enforcement has positive probability. -/
theorem enforceProb_strictAntiOn {Ξ ϱ : ℝ} (hΞ : 0 < Ξ) (hϱ : 0 < ϱ) :
    StrictAntiOn (enforceProb Ξ ϱ) {n | 0 ≤ n ∧ n ^ ϱ < Ξ} := by
  rintro a ⟨ha0, ha⟩ b ⟨hb0, hb⟩ hab
  unfold enforceProb
  have h1 : a ^ ϱ < b ^ ϱ := Real.rpow_lt_rpow ha0 hab hϱ
  have h2 : a ^ ϱ / Ξ < b ^ ϱ / Ξ := div_lt_div_of_pos_right h1 hΞ
  have hb' : b ^ ϱ / Ξ < 1 := (div_lt_one hΞ).2 hb
  have ha' : a ^ ϱ / Ξ < 1 := (div_lt_one hΞ).2 ha
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  linarith

end Chapeco.SP8
