-- Prove2me | solution 1 for BanditAlgorithm.weissman_l1_deviation
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T03:58:20.081355+00:00
-- url     : https://prove2.me/submissions/06ca31b6-ff9d-468c-ba2e-651071e99538

import Theorems.Thm_BanditAlgorithm_l1_deviation_union_bound
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The categorical `ℓ¹` concentration inequality (Weissman et al.)

`P(‖p̂_m − p‖₁ ≥ ε) ≤ 2^{|ι|} exp(−m ε² / 2)` for the empirical distribution of
`m` independent samples with law `p`.  This is the fixed-sample-size inequality
behind the confidence sets of UCRL2 (L&S Eq. 38.13, Lemma 38.8): the union bound
over the `2^{|ι|}` events is imported, and Hoeffding's inequality is applied to
the indicators of each event.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

/-- **Weissman's inequality.**  If `X 0, …, X (m-1)` are independent with common
law `p` on a finite set, then the empirical distribution deviates from `p` in
`ℓ¹` by at least `ε` with probability at most `2^{|ι|} exp(−mε²/2)`. -/
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] {m : ℕ} (hm : 0 < m)
    (X : Fin m → Ω → ι) (p : ι → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ)
    (hlaw : ∀ (i : Fin m) (a : ι), μ.real {ω | X i ω = a} = p a)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ a, |(∑ i : Fin m, if X i ω = a then (1 : ℝ) else 0) / m - p a|}
      ≤ 2 ^ Fintype.card ι * Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set phat : Ω → ι → ℝ :=
    fun ω a ↦ (∑ i : Fin m, if X i ω = a then (1 : ℝ) else 0) / m with hphat
  -- ## the empirical vector and `p` are both probability vectors
  have hone : ∀ (i : Fin m) (ω : Ω), ∑ a, (if X i ω = a then (1 : ℝ) else 0) = 1 := by
    intro i ω
    rw [Finset.sum_ite_eq]
    simp
  have hphat_sum : ∀ ω, ∑ a, phat ω a = 1 := by
    intro ω
    simp only [hphat]
    rw [← Finset.sum_div, Finset.sum_comm,
      Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) ↦ hone i ω)]
    have hcard : (∑ _i : Fin m, (1 : ℝ)) = (m : ℝ) := by simp
    rw [hcard, div_self hmR.ne']
  have hp_sum : ∑ a, p a = 1 := by
    have h1 : ∀ a, p a = μ.real (X ⟨0, hm⟩ ⁻¹' {a}) := fun a ↦ (hlaw ⟨0, hm⟩ a).symm
    calc ∑ a, p a = ∑ a ∈ (Finset.univ : Finset ι), μ.real (X ⟨0, hm⟩ ⁻¹' {a}) :=
          Finset.sum_congr rfl fun a _ ↦ h1 a
      _ = μ.real (X ⟨0, hm⟩ ⁻¹' (↑(Finset.univ : Finset ι))) :=
          sum_measureReal_preimage_singleton _
            (fun y _ ↦ (hmeas ⟨0, hm⟩) (measurableSet_singleton y))
      _ = 1 := by simp
  -- ## the per-event bound, by Hoeffding
  have hbound : ∀ A : Finset ι,
      μ.real {ω | ε / 2 ≤ ∑ a ∈ A, (phat ω a - p a)}
        ≤ Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
    intro A
    set pA : ℝ := ∑ a ∈ A, p a with hpA
    set Z : Fin m → Ω → ℝ := fun i ω ↦ if X i ω ∈ A then (1 : ℝ) else 0 with hZ
    -- the event, rewritten as a deviation of a sum of independent indicators
    have hZsum : ∀ (i : Fin m) (ω : Ω),
        ∑ a ∈ A, (if X i ω = a then (1 : ℝ) else 0) = Z i ω := by
      intro i ω
      rw [Finset.sum_ite_eq]
    have hev : ∀ ω, ∑ a ∈ A, (phat ω a - p a) = (∑ i, (Z i ω - pA)) / m := by
      intro ω
      have h1 : ∑ a ∈ A, phat ω a = (∑ i, Z i ω) / m := by
        simp only [hphat]
        rw [← Finset.sum_div, Finset.sum_comm]
        exact congrArg (· / (m : ℝ))
          (Finset.sum_congr rfl fun i _ ↦ hZsum i ω)
      rw [Finset.sum_sub_distrib, h1, ← hpA, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hset : {ω | ε / 2 ≤ ∑ a ∈ A, (phat ω a - p a)}
        = {ω | (m : ℝ) * ε / 2 ≤ ∑ i, (Z i ω - pA)} := by
      ext ω
      simp only [Set.mem_setOf_eq, hev ω]
      rw [le_div_iff₀ hmR]
      constructor <;> intro h <;> nlinarith [h]
    -- the indicators are bounded, hence sub-Gaussian
    have hZmeas : ∀ i, Measurable (Z i) := by
      intro i
      have : Z i = (fun x : ι ↦ if x ∈ A then (1 : ℝ) else 0) ∘ (X i) := rfl
      rw [this]
      exact (measurable_of_countable _).comp (hmeas i)
    have hZint : ∀ i, μ[Z i] = pA := by
      intro i
      have hZi : Z i = Set.indicator (X i ⁻¹' ↑A) 1 := by
        funext ω
        by_cases h : X i ω ∈ A
        · simp [hZ, h, Set.indicator, Set.mem_preimage]
        · simp [hZ, h, Set.indicator, Set.mem_preimage]
      rw [hZi, integral_indicator_one ((hmeas i) A.measurableSet)]
      rw [← sum_measureReal_preimage_singleton A
        (fun y _ ↦ (hmeas i) (measurableSet_singleton y))]
      exact Finset.sum_congr rfl fun a _ ↦ hlaw i a
    have hsg : ∀ i : Fin m,
        HasSubgaussianMGF (fun ω ↦ Z i ω - pA) ((1 : ℝ≥0) / 4) μ := by
      intro i
      have h := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := Z i) (a := 0) (b := 1)
        (hZmeas i).aemeasurable
        (Filter.Eventually.of_forall fun ω ↦ by
          by_cases h : X i ω ∈ A <;> simp [hZ, h])
      rw [hZint i] at h
      have hc : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = (1 : ℝ≥0) / 4 := by
        norm_num
      rwa [hc] at h
    -- independence, transported along the indicator map
    have hWindep : iIndepFun (fun i ω ↦ Z i ω - pA) μ := by
      have := hindep.comp (fun _ : Fin m ↦ fun x : ι ↦ (if x ∈ A then (1 : ℝ) else 0) - pA)
        (fun _ ↦ measurable_of_countable _)
      exact this
    -- Hoeffding
    have hHoef := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hWindep
      (c := fun _ : Fin m ↦ (1 : ℝ≥0) / 4) (s := Finset.univ)
      (fun i _ ↦ hsg i) (ε := (m : ℝ) * ε / 2) (by positivity)
    rw [hset]
    refine le_trans hHoef (le_of_eq ?_)
    congr 1
    have hsum : ((∑ _i : Fin m, ((1 : ℝ≥0) / 4) : ℝ≥0) : ℝ) = (m : ℝ) / 4 := by
      simp [Finset.sum_const, Finset.card_univ]
      push_cast
      ring
    rw [hsum]
    field_simp
    ring
  -- ## assemble with the union bound
  exact BanditAlgorithm.l1_deviation_union_bound phat p ε _ (fun ω ↦ by rw [hphat_sum ω, hp_sum]) hbound
