/-
Proposition 1 (selection), Supplementary Material 03, Section S3.1.

A party elects the `S` highest-ranked of `N` aspirants on the index `I = λ_L + t λ_B + s ε`, where
`(λ_L, λ_B)` is standard bivariate normal with correlation `ρ` and `ε` is an independent standard
normal. The proposition states that the expected legislative skill of the elected is
`r(t,s) a(S,N)`, with `r(t,s) = (1 + tρ)/√(1 + t² + 2tρ + s²)`, that `r` falls with `t` if and only
if `t > ρ s²/(1 - ρ²)`, and that closed lists raise the expected skill of the elected if and only if
`r(X t₀, σ_ν) > r(t₀, σ_ε)`.

What is formalized here:

* Step 1: the covariance algebra (`cov_skill_index`, `var_index`, `cov_brokerage_index`) and the
  conditional expectation of skill given the indices (`condExp_eq_projection`). The one property of
  the normal distribution that enters as a hypothesis is that the residual of `λ_L` after its linear
  projection on the index is independent of the indices (for jointly normal variables, zero
  correlation implies independence; Mathlib does not yet contain multivariate normal
  distributions).
* Step 2: the tower property over any selection rule that depends only on the indices
  (`expected_skill_elected`, `expected_mean_skill_elected`, and `expected_brokerage_elected` for
  brokerage skill), and the fact that the expected mean of the selected standardized indices depends
  only on their joint law, which is the same under both list rules (`selection_mean_invariant`).
* Step 3: the derivative of `r` and its sign (`hasDerivAt_corr`, `deriv_corr_neg_iff`,
  `corr_strictAntiOn`, `corr_strictMonoOn`).
* Step 4: the comparison of closed and open lists (`closed_lists_raise_skill_iff`).
-/
import ChapecoProofs.Basic

noncomputable section

open Real Filter Topology MeasureTheory ProbabilityTheory

namespace Chapeco.P1

/-! ## The correlation between skill and the index -/

/-- Variance of the index `λ_L + t λ_B + s ε`: `D = 1 + t² + 2tρ + s²`. -/
def D (ρ t s : ℝ) : ℝ := 1 + t ^ 2 + 2 * t * ρ + s ^ 2

/-- Correlation between legislative skill and the index: `r(t,s) = (1 + tρ)/√D`. -/
def corr (ρ t s : ℝ) : ℝ := (1 + t * ρ) / Real.sqrt (D ρ t s)

/-- Correlation between brokerage skill and the index: `r_B = (t + ρ)/√D`. -/
def corrB (ρ t s : ℝ) : ℝ := (t + ρ) / Real.sqrt (D ρ t s)

theorem D_eq (ρ t s : ℝ) : D ρ t s = (t + ρ) ^ 2 + (1 - ρ ^ 2) + s ^ 2 := by
  unfold D
  ring

theorem D_pos {ρ : ℝ} (hρ : ρ ^ 2 < 1) (t s : ℝ) : 0 < D ρ t s := by
  rw [D_eq]
  nlinarith [sq_nonneg (t + ρ), sq_nonneg s]

/-! ## Step 1: covariances and the conditional expectation -/

/-- The index of an aspirant, `I = λ_L + t λ_B + s ε`. -/
def index {Ω : Type*} (L B E : Ω → ℝ) (t s : ℝ) : Ω → ℝ := fun ω => L ω + t * B ω + s * E ω

theorem index_eq {Ω : Type*} (L B E : Ω → ℝ) (t s : ℝ) : index L B E t s = L + t • B + s • E := by
  funext ω
  simp [index, smul_eq_mul]

section Covariance

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem memLp_index {L B E : Ω → ℝ} (hL : MemLp L 2 μ) (hB : MemLp B 2 μ) (hE : MemLp E 2 μ)
    (t s : ℝ) : MemLp (index L B E t s) 2 μ := by
  rw [index_eq]
  exact (hL.add (hB.const_smul t)).add (hE.const_smul s)

theorem cov_index_right {X L B E : Ω → ℝ} (hX : MemLp X 2 μ) (hL : MemLp L 2 μ)
    (hB : MemLp B 2 μ) (hE : MemLp E 2 μ) (t s : ℝ) :
    cov[X, index L B E t s; μ] = cov[X, L; μ] + t * cov[X, B; μ] + s * cov[X, E; μ] := by
  rw [index_eq, covariance_add_right hX (hL.add (hB.const_smul t)) (hE.const_smul s),
    covariance_add_right hX hL (hB.const_smul t), covariance_smul_right, covariance_smul_right]

/-- `Cov(λ_L, I) = 1 + tρ`. -/
theorem cov_skill_index {L B E : Ω → ℝ} {ρ : ℝ} (hL : MemLp L 2 μ) (hB : MemLp B 2 μ)
    (hE : MemLp E 2 μ) (hLL : Var[L; μ] = 1) (hLB : cov[L, B; μ] = ρ) (hLE : cov[L, E; μ] = 0)
    (t s : ℝ) : cov[L, index L B E t s; μ] = 1 + t * ρ := by
  rw [cov_index_right hL hL hB hE, covariance_same hL.aestronglyMeasurable.aemeasurable, hLL, hLB,
    hLE]
  ring

/-- `Cov(λ_B, I) = t + ρ`. -/
theorem cov_brokerage_index {L B E : Ω → ℝ} {ρ : ℝ} (hL : MemLp L 2 μ) (hB : MemLp B 2 μ)
    (hE : MemLp E 2 μ) (hBB : Var[B; μ] = 1) (hLB : cov[L, B; μ] = ρ) (hBE : cov[B, E; μ] = 0)
    (t s : ℝ) : cov[B, index L B E t s; μ] = t + ρ := by
  rw [cov_index_right hB hL hB hE, covariance_same hB.aestronglyMeasurable.aemeasurable,
    covariance_comm B L, hBB, hLB, hBE]
  ring

/-- `Var(I) = D = 1 + t² + 2tρ + s²`. -/
theorem var_index {L B E : Ω → ℝ} {ρ : ℝ} (hL : MemLp L 2 μ) (hB : MemLp B 2 μ)
    (hE : MemLp E 2 μ) (hLL : Var[L; μ] = 1) (hBB : Var[B; μ] = 1) (hEE : Var[E; μ] = 1)
    (hLB : cov[L, B; μ] = ρ) (hLE : cov[L, E; μ] = 0) (hBE : cov[B, E; μ] = 0) (t s : ℝ) :
    Var[index L B E t s; μ] = D ρ t s := by
  have hI := memLp_index hL hB hE t s
  rw [← covariance_same hI.aestronglyMeasurable.aemeasurable, cov_index_right hI hL hB hE,
    covariance_comm _ L, covariance_comm _ B, covariance_comm _ E,
    cov_index_right hL hL hB hE, cov_index_right hB hL hB hE, cov_index_right hE hL hB hE,
    covariance_same hL.aestronglyMeasurable.aemeasurable,
    covariance_same hB.aestronglyMeasurable.aemeasurable,
    covariance_same hE.aestronglyMeasurable.aemeasurable, covariance_comm B L, covariance_comm E L,
    covariance_comm E B, hLL, hBB, hEE, hLB, hLE, hBE]
  unfold D
  ring

/-- The linear projection of skill on the index, written with the standardized index
`Ĩ = I/√D`: `((1 + tρ)/D) x = r(t,s) (x/√D)`. -/
theorem projection_coeff {ρ : ℝ} (hρ : ρ ^ 2 < 1) (t s x : ℝ) :
    (1 + t * ρ) / D ρ t s * x = corr ρ t s * (x / Real.sqrt (D ρ t s)) := by
  have hD := D_pos hρ t s
  have hsq : Real.sqrt (D ρ t s) * Real.sqrt (D ρ t s) = D ρ t s := Real.mul_self_sqrt hD.le
  unfold corr
  rw [div_mul_div_comm, hsq, div_mul_eq_mul_div]

/-- **Step 1 (conditional expectation).** If `I` is measurable with respect to the σ-algebra `m`
of the indices, and the residual `L - β I` has mean zero and is measurable with respect to a
σ-algebra `m₁` independent of `m`, then `𝔼[L | m] = β I`. -/
theorem condExp_eq_projection {m m₁ : MeasurableSpace Ω} (hm : m ≤ mΩ) (hm₁ : m₁ ≤ mΩ)
    {L I : Ω → ℝ} {β : ℝ} (hL : Integrable L μ) (hI : Integrable I μ)
    (hIm : StronglyMeasurable[m] I)
    (hU : StronglyMeasurable[m₁] fun ω => L ω - β * I ω) (hindep : Indep m₁ m μ)
    (hmean : ∫ ω, (L ω - β * I ω) ∂μ = 0) :
    μ[L|m] =ᵐ[μ] fun ω => β * I ω := by
  have hsplit : L = (fun ω => L ω - β * I ω) + β • I := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hUint : Integrable (fun ω => L ω - β * I ω) μ := hL.sub (hI.const_mul β)
  have h1 : μ[fun ω => L ω - β * I ω|m] =ᵐ[μ] fun _ => (0 : ℝ) := by
    filter_upwards [condExp_indep_eq hm₁ hm hU hindep] with ω hω
    rw [hω]
    exact hmean
  have h2 : μ[β • I|m] = β • I :=
    condExp_of_stronglyMeasurable hm (hIm.const_smul β) (hI.smul β)
  rw [hsplit]
  refine (condExp_add hUint (hI.smul β) m).trans ?_
  rw [h2]
  filter_upwards [h1] with ω hω
  simp [hω]

/-! ## Step 2: the elected -/

/-- **Proposition 1, Steps 1 and 2.** For every aspirant `i`, legislative skill `L i`, brokerage
skill `B i` and the noise `E i` are square integrable, with mean zero, unit variances,
`Cov(L i, B i) = ρ` and the noise uncorrelated with both. The σ-algebra `m` is generated by the
indices; the residual of `L i` after its linear projection on its index is independent of `m`.
Then for any selection rule that depends only on the indices (the events `A i`, "aspirant `i` is
elected", are `m`-measurable), the expected total legislative skill of the elected is
`r(t,s)` times the expected total standardized index of the elected. -/
theorem expected_skill_elected {ι : Type*} (N : Finset ι) {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {ρ t s : ℝ} (hρ : ρ ^ 2 < 1) (L B E : ι → Ω → ℝ)
    (hL : ∀ i, MemLp (L i) 2 μ) (hB : ∀ i, MemLp (B i) 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hL0 : ∀ i, ∫ ω, L i ω ∂μ = 0) (hB0 : ∀ i, ∫ ω, B i ω ∂μ = 0)
    (hE0 : ∀ i, ∫ ω, E i ω ∂μ = 0)
    (hLL : ∀ i, Var[L i; μ] = 1) (hBB : ∀ i, Var[B i; μ] = 1) (hEE : ∀ i, Var[E i; μ] = 1)
    (hLB : ∀ i, cov[L i, B i; μ] = ρ) (hLE : ∀ i, cov[L i, E i; μ] = 0)
    (hBE : ∀ i, cov[B i, E i; μ] = 0)
    (hIm : ∀ i, StronglyMeasurable[m] (index (L i) (B i) (E i) t s))
    (mU : ι → MeasurableSpace Ω) (hmU : ∀ i, mU i ≤ mΩ)
    (hU : ∀ i, StronglyMeasurable[mU i] fun ω => L i ω -
      cov[L i, index (L i) (B i) (E i) t s; μ] / Var[index (L i) (B i) (E i) t s; μ] *
        index (L i) (B i) (E i) t s ω)
    (hindep : ∀ i, Indep (mU i) m μ)
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet[m] (A i)) :
    ∑ i ∈ N, ∫ ω in A i, L i ω ∂μ =
      corr ρ t s * ∑ i ∈ N, ∫ ω in A i, index (L i) (B i) (E i) t s ω / Real.sqrt (D ρ t s) ∂μ := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hLi : Integrable (L i) μ := (hL i).integrable (by norm_num)
  have hIi : Integrable (index (L i) (B i) (E i) t s) μ :=
    (memLp_index (hL i) (hB i) (hE i) t s).integrable (by norm_num)
  have hcov := cov_skill_index (hL i) (hB i) (hE i) (hLL i) (hLB i) (hLE i) t s
  have hvar := var_index (hL i) (hB i) (hE i) (hLL i) (hBB i) (hEE i) (hLB i) (hLE i) (hBE i) t s
  have hUi := hU i
  rw [hcov, hvar] at hUi
  have hBi : Integrable (B i) μ := (hB i).integrable (by norm_num)
  have hEi : Integrable (E i) μ := (hE i).integrable (by norm_num)
  have hmean : ∫ ω, (L i ω - (1 + t * ρ) / D ρ t s * index (L i) (B i) (E i) t s ω) ∂μ = 0 := by
    have hI0 : ∫ ω, index (L i) (B i) (E i) t s ω ∂μ = 0 := by
      have h1 : Integrable (fun ω => L i ω + t * B i ω) μ := hLi.add (hBi.const_mul t)
      have h2 : Integrable (fun ω => s * E i ω) μ := hEi.const_mul s
      have h3 : Integrable (fun ω => t * B i ω) μ := hBi.const_mul t
      simp only [index]
      rw [integral_add h1 h2, integral_add hLi h3, integral_const_mul, integral_const_mul,
        hL0 i, hB0 i, hE0 i]
      ring
    rw [integral_sub hLi (hIi.const_mul _), integral_const_mul, hI0, hL0 i]
    ring
  have hproj := condExp_eq_projection hm (hmU i) hLi hIi (hIm i) hUi (hindep i) hmean
  calc ∫ ω in A i, L i ω ∂μ = ∫ ω in A i, (μ[L i|m]) ω ∂μ :=
        (setIntegral_condExp hm hLi (hA i)).symm
    _ = ∫ ω in A i, (1 + t * ρ) / D ρ t s * index (L i) (B i) (E i) t s ω ∂μ :=
        setIntegral_congr_ae (hm _ (hA i)) (hproj.mono fun ω hω _ => hω)
    _ = ∫ ω in A i, corr ρ t s * (index (L i) (B i) (E i) t s ω / Real.sqrt (D ρ t s)) ∂μ := by
        simp_rw [projection_coeff hρ t s]
    _ = corr ρ t s * ∫ ω in A i, index (L i) (B i) (E i) t s ω / Real.sqrt (D ρ t s) ∂μ :=
        integral_const_mul _ _

/-- **Proposition 1, equation of the elected.** The same statement for the mean over the `S`
elected: `𝔼[mean skill of the elected] = r(t,s) 𝔼[mean standardized index of the elected]`; the
right-hand expectation is `a(S,N)` when the rule elects the `S` highest-ranked aspirants. -/
theorem expected_mean_skill_elected {ι : Type*} (N : Finset ι) {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {ρ t s : ℝ} (hρ : ρ ^ 2 < 1) (L B E : ι → Ω → ℝ)
    (hL : ∀ i, MemLp (L i) 2 μ) (hB : ∀ i, MemLp (B i) 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hL0 : ∀ i, ∫ ω, L i ω ∂μ = 0) (hB0 : ∀ i, ∫ ω, B i ω ∂μ = 0)
    (hE0 : ∀ i, ∫ ω, E i ω ∂μ = 0)
    (hLL : ∀ i, Var[L i; μ] = 1) (hBB : ∀ i, Var[B i; μ] = 1) (hEE : ∀ i, Var[E i; μ] = 1)
    (hLB : ∀ i, cov[L i, B i; μ] = ρ) (hLE : ∀ i, cov[L i, E i; μ] = 0)
    (hBE : ∀ i, cov[B i, E i; μ] = 0)
    (hIm : ∀ i, StronglyMeasurable[m] (index (L i) (B i) (E i) t s))
    (mU : ι → MeasurableSpace Ω) (hmU : ∀ i, mU i ≤ mΩ)
    (hU : ∀ i, StronglyMeasurable[mU i] fun ω => L i ω -
      cov[L i, index (L i) (B i) (E i) t s; μ] / Var[index (L i) (B i) (E i) t s; μ] *
        index (L i) (B i) (E i) t s ω)
    (hindep : ∀ i, Indep (mU i) m μ)
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet[m] (A i)) (S : ℝ) :
    ∫ ω, (∑ i ∈ N, (A i).indicator (L i) ω) / S ∂μ =
      corr ρ t s * ∫ ω, (∑ i ∈ N, (A i).indicator
        (fun ω => index (L i) (B i) (E i) t s ω / Real.sqrt (D ρ t s)) ω) / S ∂μ := by
  letI := mΩ
  have hLi : ∀ i ∈ N, Integrable ((A i).indicator (L i)) μ := fun i _ =>
    ((hL i).integrable (by norm_num)).indicator (hm _ (hA i))
  have hJi : ∀ i ∈ N, Integrable ((A i).indicator
      (fun ω => index (L i) (B i) (E i) t s ω / Real.sqrt (D ρ t s))) μ := fun i _ =>
    (((memLp_index (hL i) (hB i) (hE i) t s).integrable (by norm_num)).div_const _).indicator
      (hm _ (hA i))
  have h1 : ∀ i ∈ N, ∫ ω, (A i).indicator (L i) ω ∂μ = ∫ ω in A i, L i ω ∂μ := fun i _ =>
    integral_indicator (hm _ (hA i))
  have h2 : ∀ i ∈ N, ∫ ω, (A i).indicator
      (fun ω => index (L i) (B i) (E i) t s ω / Real.sqrt (D ρ t s)) ω ∂μ =
        ∫ ω in A i, index (L i) (B i) (E i) t s ω / Real.sqrt (D ρ t s) ∂μ := fun i _ =>
    integral_indicator (hm _ (hA i))
  rw [integral_div, integral_div, integral_finset_sum N hLi, integral_finset_sum N hJi,
    Finset.sum_congr rfl h1, Finset.sum_congr rfl h2,
    expected_skill_elected N hm hρ L B E hL hB hE hL0 hB0 hE0 hLL hBB hEE hLB hLE hBE hIm mU
      hmU hU hindep A hA, mul_div_assoc]

/-- The tower step for any variable `X` whose conditional mean given the indices is `c J`: over any
selection rule that depends only on the indices, `𝔼[∑ elected X] = c 𝔼[∑ elected J]`. -/
theorem sum_setIntegral_eq_of_condExp {ι : Type*} (N : Finset ι) {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {X J : ι → Ω → ℝ} {c : ℝ} (hX : ∀ i, Integrable (X i) μ)
    (hproj : ∀ i, μ[X i|m] =ᵐ[μ] fun ω => c * J i ω)
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet[m] (A i)) :
    ∑ i ∈ N, ∫ ω in A i, X i ω ∂μ = c * ∑ i ∈ N, ∫ ω in A i, J i ω ∂μ := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc ∫ ω in A i, X i ω ∂μ = ∫ ω in A i, (μ[X i|m]) ω ∂μ :=
        (setIntegral_condExp hm (hX i) (hA i)).symm
    _ = ∫ ω in A i, c * J i ω ∂μ :=
        setIntegral_congr_ae (hm _ (hA i)) ((hproj i).mono fun ω hω _ => hω)
    _ = c * ∫ ω in A i, J i ω ∂μ := integral_const_mul _ _

/-- The linear projection of brokerage skill on the index, with the standardized index:
`((t + ρ)/D) x = r_B (x/√D)`. -/
theorem projection_coeff_brokerage {ρ : ℝ} (hρ : ρ ^ 2 < 1) (t s x : ℝ) :
    (t + ρ) / D ρ t s * x = corrB ρ t s * (x / Real.sqrt (D ρ t s)) := by
  have hD := D_pos hρ t s
  have hsq : Real.sqrt (D ρ t s) * Real.sqrt (D ρ t s) = D ρ t s := Real.mul_self_sqrt hD.le
  unfold corrB
  rw [div_mul_div_comm, hsq, div_mul_eq_mul_div]

/-- **Proposition 1, Step 2 (brokerage skill).** Under the same assumptions, with the residual of
brokerage skill after its projection on the index independent of the indices, the expected total
brokerage skill of the elected is `r_B = (t + ρ)/√D` times the expected total standardized index of
the elected, so `𝔼[λ_B | elected] = r_B a(S,N)`. -/
theorem expected_brokerage_elected {ι : Type*} (N : Finset ι) {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {ρ t s : ℝ} (hρ : ρ ^ 2 < 1) (L B E : ι → Ω → ℝ)
    (hL : ∀ i, MemLp (L i) 2 μ) (hB : ∀ i, MemLp (B i) 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hL0 : ∀ i, ∫ ω, L i ω ∂μ = 0) (hB0 : ∀ i, ∫ ω, B i ω ∂μ = 0)
    (hE0 : ∀ i, ∫ ω, E i ω ∂μ = 0)
    (hLL : ∀ i, Var[L i; μ] = 1) (hBB : ∀ i, Var[B i; μ] = 1) (hEE : ∀ i, Var[E i; μ] = 1)
    (hLB : ∀ i, cov[L i, B i; μ] = ρ) (hLE : ∀ i, cov[L i, E i; μ] = 0)
    (hBE : ∀ i, cov[B i, E i; μ] = 0)
    (hIm : ∀ i, StronglyMeasurable[m] (index (L i) (B i) (E i) t s))
    (mU : ι → MeasurableSpace Ω) (hmU : ∀ i, mU i ≤ mΩ)
    (hU : ∀ i, StronglyMeasurable[mU i] fun ω => B i ω -
      cov[B i, index (L i) (B i) (E i) t s; μ] / Var[index (L i) (B i) (E i) t s; μ] *
        index (L i) (B i) (E i) t s ω)
    (hindep : ∀ i, Indep (mU i) m μ)
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet[m] (A i)) :
    ∑ i ∈ N, ∫ ω in A i, B i ω ∂μ =
      corrB ρ t s *
        ∑ i ∈ N, ∫ ω in A i, index (L i) (B i) (E i) t s ω / Real.sqrt (D ρ t s) ∂μ := by
  refine sum_setIntegral_eq_of_condExp N hm (fun i => (hB i).integrable (by norm_num))
    (fun i => ?_) A hA
  have hLi : Integrable (L i) μ := (hL i).integrable (by norm_num)
  have hBi : Integrable (B i) μ := (hB i).integrable (by norm_num)
  have hEi : Integrable (E i) μ := (hE i).integrable (by norm_num)
  have hIi : Integrable (index (L i) (B i) (E i) t s) μ :=
    (memLp_index (hL i) (hB i) (hE i) t s).integrable (by norm_num)
  have hcov := cov_brokerage_index (hL i) (hB i) (hE i) (hBB i) (hLB i) (hBE i) t s
  have hvar := var_index (hL i) (hB i) (hE i) (hLL i) (hBB i) (hEE i) (hLB i) (hLE i) (hBE i) t s
  have hUi := hU i
  rw [hcov, hvar] at hUi
  have hmean : ∫ ω, (B i ω - (t + ρ) / D ρ t s * index (L i) (B i) (E i) t s ω) ∂μ = 0 := by
    have hI0 : ∫ ω, index (L i) (B i) (E i) t s ω ∂μ = 0 := by
      have h1 : Integrable (fun ω => L i ω + t * B i ω) μ := hLi.add (hBi.const_mul t)
      have h2 : Integrable (fun ω => s * E i ω) μ := hEi.const_mul s
      have h3 : Integrable (fun ω => t * B i ω) μ := hBi.const_mul t
      simp only [index]
      rw [integral_add h1 h2, integral_add hLi h3, integral_const_mul, integral_const_mul,
        hL0 i, hB0 i, hE0 i]
      ring
    rw [integral_sub hBi (hIi.const_mul _), integral_const_mul, hI0, hB0 i]
    ring
  have hproj := condExp_eq_projection hm (hmU i) hBi hIi (hIm i) hUi (hindep i) hmean
  filter_upwards [hproj] with ω hω
  rw [hω, projection_coeff_brokerage hρ t s]

omit [IsProbabilityMeasure μ] in
/-- **Step 2 (the factor `a(S,N)`).** The expected value of any measurable function of the vector of
standardized indices, in particular the mean of the `S` largest, depends only on the joint law of
the vector. Under both list rules the standardized indices are independent standard normal, so
`a(S,N)` is the same under both rules. -/
theorem selection_mean_invariant {ι : Type*} [Fintype ι] {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {μ' : Measure Ω'} (J : Ω → ι → ℝ) (J' : Ω' → ι → ℝ) (hJ : AEMeasurable J μ)
    (hJ' : AEMeasurable J' μ')
    (hlaw : μ.map J = Measure.pi fun _ => gaussianReal 0 1)
    (hlaw' : μ'.map J' = Measure.pi fun _ => gaussianReal 0 1)
    (g : (ι → ℝ) → ℝ) (hg : Measurable g) :
    ∫ ω, g (J ω) ∂μ = ∫ ω, g (J' ω) ∂μ' := by
  rw [← integral_map hJ hg.aestronglyMeasurable, ← integral_map hJ' hg.aestronglyMeasurable,
    hlaw, hlaw']

end Covariance

/-! ## Step 3: how `r` varies with the weight on brokerage -/

theorem hasDerivAt_D (ρ t s : ℝ) : HasDerivAt (fun t => D ρ t s) (2 * t + 2 * ρ) t := by
  have h := ((((hasDerivAt_pow 2 t).const_add 1).add
    (((hasDerivAt_id' t).const_mul 2).mul_const ρ)).add_const (s ^ 2))
  refine h.congr_deriv ?_
  norm_num

/-- **Step 3.** `∂r/∂t = D^{-3/2} [ρ s² - t (1 - ρ²)]`. -/
theorem hasDerivAt_corr {ρ : ℝ} (hρ : ρ ^ 2 < 1) (t s : ℝ) :
    HasDerivAt (fun t => corr ρ t s)
      ((ρ * s ^ 2 - t * (1 - ρ ^ 2)) / Real.sqrt (D ρ t s) ^ 3) t := by
  have hD := D_pos hρ t s
  have hnum : HasDerivAt (fun y => 1 + y * ρ) (1 * ρ) t :=
    ((hasDerivAt_id' t).mul_const ρ).const_add 1
  have hden : HasDerivAt (fun y => Real.sqrt (D ρ y s))
      ((2 * t + 2 * ρ) / (2 * Real.sqrt (D ρ t s))) t :=
    (hasDerivAt_D ρ t s).sqrt hD.ne'
  have hq : 0 < Real.sqrt (D ρ t s) := Real.sqrt_pos.2 hD
  have hdiv := hnum.div hden hq.ne'
  show HasDerivAt (fun y => (1 + y * ρ) / Real.sqrt (D ρ y s)) _ t
  refine hdiv.congr_deriv ?_
  have hqD : D ρ t s = Real.sqrt (D ρ t s) ^ 2 := (Real.sq_sqrt hD.le).symm
  have key : ρ * s ^ 2 - t * (1 - ρ ^ 2) =
      ρ * Real.sqrt (D ρ t s) ^ 2 - (1 + t * ρ) * (t + ρ) := by
    rw [← hqD]
    unfold D
    ring
  rw [key]
  generalize Real.sqrt (D ρ t s) = q at hq ⊢
  have hq' : q ≠ 0 := hq.ne'
  field_simp
  ring

theorem deriv_corr_neg_iff {ρ : ℝ} (hρ : ρ ^ 2 < 1) (t s : ℝ) :
    (ρ * s ^ 2 - t * (1 - ρ ^ 2)) / Real.sqrt (D ρ t s) ^ 3 < 0 ↔
      ρ * s ^ 2 / (1 - ρ ^ 2) < t := by
  have hq : 0 < Real.sqrt (D ρ t s) ^ 3 := pow_pos (Real.sqrt_pos.2 (D_pos hρ t s)) 3
  have h1 : 0 < 1 - ρ ^ 2 := by linarith
  rw [div_lt_iff₀ hq, zero_mul, div_lt_iff₀ h1]
  constructor <;> intro h <;> linarith

theorem deriv_corr_pos_iff {ρ : ℝ} (hρ : ρ ^ 2 < 1) (t s : ℝ) :
    0 < (ρ * s ^ 2 - t * (1 - ρ ^ 2)) / Real.sqrt (D ρ t s) ^ 3 ↔
      t < ρ * s ^ 2 / (1 - ρ ^ 2) := by
  have hq : 0 < Real.sqrt (D ρ t s) ^ 3 := pow_pos (Real.sqrt_pos.2 (D_pos hρ t s)) 3
  have h1 : 0 < 1 - ρ ^ 2 := by linarith
  rw [lt_div_iff₀ hq, zero_mul, lt_div_iff₀ h1]
  constructor <;> intro h <;> linarith

/-- `r` falls with `t` for `t ≥ ρ s²/(1 - ρ²)`. -/
theorem corr_strictAntiOn {ρ : ℝ} (hρ : ρ ^ 2 < 1) (s : ℝ) :
    StrictAntiOn (fun t => corr ρ t s) (Set.Ici (ρ * s ^ 2 / (1 - ρ ^ 2))) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · exact fun t _ => (hasDerivAt_corr hρ t s).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    rw [(hasDerivAt_corr hρ t s).deriv]
    exact (deriv_corr_neg_iff hρ t s).2 ht

/-- `r` rises with `t` for `t ≤ ρ s²/(1 - ρ²)`. -/
theorem corr_strictMonoOn {ρ : ℝ} (hρ : ρ ^ 2 < 1) (s : ℝ) :
    StrictMonoOn (fun t => corr ρ t s) (Set.Iic (ρ * s ^ 2 / (1 - ρ ^ 2))) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic _)
  · exact fun t _ => (hasDerivAt_corr hρ t s).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Iic] at ht
    rw [(hasDerivAt_corr hρ t s).deriv]
    exact (deriv_corr_pos_iff hρ t s).2 ht

/-! ## Step 4: closed against open lists -/

/-- **Step 4.** With the same `a(S,N) > 0` under both rules, closed lists (weight `X t₀`, noise
`σ_ν`) raise the expected legislative skill of the elected over open lists (weight `t₀`, noise
`σ_ε`) if and only if `r(X t₀, σ_ν) > r(t₀, σ_ε)`. -/
theorem closed_lists_raise_skill_iff {a : ℝ} (ha : 0 < a) (ρ t₀ X σν σε : ℝ) :
    corr ρ t₀ σε * a < corr ρ (X * t₀) σν * a ↔ corr ρ t₀ σε < corr ρ (X * t₀) σν :=
  mul_lt_mul_right ha

end Chapeco.P1
