-- Prove2me | solution 1 for mme_stothers_slice_entropy_minimum_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-21T23:27:54.04231+00:00
-- url     : https://prove2.me/submissions/b939737b-5d45-47cb-aac3-595854dbe91e

import Definitions.Def_mme_stothers_fourth_data
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MME.StothersFourth BigOperators

set_option autoImplicit false

private theorem inY_iff_coordinates (d : Fin 10 → ℝ) :
    InY d ↔ ∀ i, d i = d 2 * kernelSigma i + d 3 * kernelTau i := by
  constructor
  · rintro ⟨s, t, h⟩
    have hs := h 2
    have ht := h 3
    change d 2 = s * 1 + t * 0 at hs
    change d 3 = s * 0 + t * 1 at ht
    simp only [mul_one, mul_zero, add_zero, zero_add] at hs ht
    simpa only [hs, ht] using h
  · exact fun h ↦ ⟨d 2, d 3, h⟩

private theorem entropyProduct_eq_exp (b : Fin 10 → ℝ) (hb : ∀ i, 0 ≤ b i) :
    entropyProduct b = Real.exp (∑ i, (classMultiplicity i : ℝ) *
      (b i * Real.log (b i))) := by
  rw [entropyProduct, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rcases (hb i).eq_or_lt with hz | hp
  · simp [← hz]
  · exact (Real.rpow_def_of_pos hp _).trans (congrArg Real.exp (by ring))

private theorem inZ_coordinate_le_one (b : Fin 10 → ℝ) (hb : InZ b) (i : Fin 10) :
    b i ≤ 1 := by
  have hw : (1 : ℝ) ≤ classMultiplicity i := by
    fin_cases i <;> norm_num [classMultiplicity]
  calc
    b i ≤ (classMultiplicity i : ℝ) * b i := by nlinarith [hb.1 i]
    _ ≤ ∑ j, (classMultiplicity j : ℝ) * b j :=
      Finset.single_le_sum (fun j _ ↦ mul_nonneg (Nat.cast_nonneg _) (hb.1 j))
        (Finset.mem_univ i)
    _ = 1 := hb.2

/-- The entropy minimum is attained even when the marginal slice meets the boundary. -/
theorem mme_stothers_slice_entropy_minimum_exists
    (a : Fin 10 → ℝ) (ha : InZ a) :
    ∃ b : Fin 10 → ℝ, InZ b ∧ InY (fun i ↦ b i - a i) ∧
      ∀ c : Fin 10 → ℝ, InZ c → InY (fun i ↦ c i - a i) →
        entropyProduct b ≤ entropyProduct c := by
  let S : Set (Fin 10 → ℝ) := {b | InZ b ∧ InY (fun i ↦ b i - a i)}
  have hclosed : IsClosed S := by
    have hz : IsClosed {b : Fin 10 → ℝ | InZ b} := by
      change IsClosed ({b : Fin 10 → ℝ | ∀ i, 0 ≤ b i} ∩
        {b | ∑ i, (classMultiplicity i : ℝ) * b i = 1})
      apply IsClosed.inter
      · simp only [Set.setOf_forall]
        exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)
      · exact isClosed_eq (by fun_prop) continuous_const
    have hy : IsClosed {b : Fin 10 → ℝ | InY (fun i ↦ b i - a i)} := by
      simp_rw [inY_iff_coordinates, Set.setOf_forall]
      exact isClosed_iInter fun i ↦ isClosed_eq (by fun_prop) (by fun_prop)
    exact hz.inter hy
  have hcompact : IsCompact S :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : Fin 10 → ℝ) 1)).of_isClosed_subset
      hclosed (fun b hb ↦ ⟨hb.1.1, inZ_coordinate_le_one b hb.1⟩)
  have haS : a ∈ S := ⟨ha, 0, 0, by intro i; simp⟩
  have hcont : Continuous (fun b : Fin 10 → ℝ ↦
      ∑ i, (classMultiplicity i : ℝ) * (b i * Real.log (b i))) := by
    fun_prop
  obtain ⟨b, hb, hmin⟩ := hcompact.exists_isMinOn ⟨a, haS⟩ hcont.continuousOn
  refine ⟨b, hb.1, hb.2, fun c hc hca ↦ ?_⟩
  rw [entropyProduct_eq_exp b hb.1.1, entropyProduct_eq_exp c hc.1]
  exact Real.exp_le_exp.mpr (hmin ⟨hc, hca⟩)

private theorem strictConvexOn_entropySum :
    StrictConvexOn ℝ {b : Fin 10 → ℝ | ∀ i, 0 ≤ b i}
      (fun b ↦ ∑ i, (classMultiplicity i : ℝ) * (b i * Real.log (b i))) := by
  have hw : ∀ i, 0 < (classMultiplicity i : ℝ) := by
    intro i
    fin_cases i <;> norm_num [classMultiplicity]
  constructor
  · intro x hx y hy p q hp hq _ i
    exact add_nonneg (mul_nonneg hp (hx i)) (mul_nonneg hq (hy i))
  · intro x hx y hy hne p q hp hq hpq
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := Function.ne_iff.mp hne
    calc
      _ < ∑ i, (classMultiplicity i : ℝ) *
          (p * (x i * Real.log (x i)) + q * (y i * Real.log (y i))) := by
        apply Finset.sum_lt_sum
        · intro i _
          exact mul_le_mul_of_nonneg_left
            (Real.convexOn_mul_log.2 (hx i) (hy i) hp.le hq.le hpq) (hw i).le
        · exact ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left
            (Real.strictConvexOn_mul_log.2 (hx j) (hy j) hj hp hq hpq) (hw j)⟩
      _ = _ := by
        simp only [smul_eq_mul, mul_add, Finset.sum_add_distrib]
        simp_rw [← mul_assoc, mul_comm _ p, mul_comm _ q, mul_assoc]
        rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- Every nonempty marginal slice has a unique entropy minimizer, including its boundary. -/
theorem solution
    (a : Fin 10 → ℝ) (ha : InZ a) :
    ∃! b : Fin 10 → ℝ, InZ b ∧ InY (fun i ↦ b i - a i) ∧
      ∀ c : Fin 10 → ℝ, InZ c → InY (fun i ↦ c i - a i) →
        entropyProduct b ≤ entropyProduct c := by
  obtain ⟨b, hb, hba, hbmin⟩ := mme_stothers_slice_entropy_minimum_exists a ha
  refine ⟨b, ⟨hb, hba, hbmin⟩, ?_⟩
  rintro c ⟨hc, hca, hcmin⟩
  by_contra hne
  let m : Fin 10 → ℝ := fun i ↦ (1 / 2 : ℝ) * c i + (1 / 2 : ℝ) * b i
  have hmZ : InZ m := by
    refine ⟨fun i ↦ add_nonneg (mul_nonneg (by norm_num) (hc.1 i))
      (mul_nonneg (by norm_num) (hb.1 i)), ?_⟩
    dsimp [m]
    simp_rw [mul_add, ← mul_assoc, mul_comm _ (1 / 2 : ℝ), mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hc.2, hb.2]
    norm_num
  have hmY : InY (fun i ↦ m i - a i) := by
    obtain ⟨s, t, hst⟩ := hca
    obtain ⟨u, v, huv⟩ := hba
    refine ⟨(s + u) / 2, (t + v) / 2, fun i ↦ ?_⟩
    dsimp [m]
    linear_combination (1 / 2 : ℝ) * hst i + (1 / 2 : ℝ) * huv i
  have hbm := hbmin m hmZ hmY
  have hcm := hcmin m hmZ hmY
  rw [entropyProduct_eq_exp b hb.1, entropyProduct_eq_exp m hmZ.1,
    Real.exp_le_exp] at hbm
  rw [entropyProduct_eq_exp c hc.1, entropyProduct_eq_exp m hmZ.1,
    Real.exp_le_exp] at hcm
  have hlt := strictConvexOn_entropySum.2 hc.1 hb.1 hne
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  change (∑ i, (classMultiplicity i : ℝ) * (m i * Real.log (m i))) <
    (1 / 2 : ℝ) * (∑ i, (classMultiplicity i : ℝ) * (c i * Real.log (c i))) +
    (1 / 2 : ℝ) * (∑ i, (classMultiplicity i : ℝ) * (b i * Real.log (b i))) at hlt
  linarith
