-- Prove2me | solution 1 for mme_stothers_slice_entropy_minimum_support
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-21T23:31:51.390463+00:00
-- url     : https://prove2.me/submissions/c04d4af6-8834-42a2-9bdd-58159cd9322c

import Definitions.Def_mme_stothers_fourth_data
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MME.StothersFourth BigOperators
set_option autoImplicit false

private theorem entropyProduct_eq_exp (b : Fin 10 → ℝ) (hb : ∀ i, 0 ≤ b i) :
    entropyProduct b = Real.exp (∑ i, (classMultiplicity i : ℝ) *
      (b i * Real.log (b i))) := by
  rw [entropyProduct, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rcases (hb i).eq_or_lt with hz | hp
  · simp [← hz]
  · exact (Real.rpow_def_of_pos hp _).trans (congrArg Real.exp (by ring))

/-- A zero coordinate gives an explicit improvement over the convexity bound. -/
private theorem entropy_mixture_bound
    (a b : Fin 10 → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (k : Fin 10) (hak : 0 < a k) (hbk : b k = 0)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    (∑ i, (classMultiplicity i : ℝ) *
      (((1 - t) * b i + t * a i) * Real.log ((1 - t) * b i + t * a i))) ≤
      (1 - t) * (∑ i, (classMultiplicity i : ℝ) * (b i * Real.log (b i))) +
      t * (∑ i, (classMultiplicity i : ℝ) * (a i * Real.log (a i))) +
      t * (classMultiplicity k : ℝ) * a k * Real.log t := by
  have hconv (i : Fin 10) :
      (classMultiplicity i : ℝ) *
        (((1 - t) * b i + t * a i) * Real.log ((1 - t) * b i + t * a i)) ≤
      (classMultiplicity i : ℝ) *
        ((1 - t) * (b i * Real.log (b i)) + t * (a i * Real.log (a i))) :=
    mul_le_mul_of_nonneg_left
      (Real.convexOn_mul_log.2 (hb i) (ha i) (sub_nonneg.mpr ht1) ht.le (by ring))
      (Nat.cast_nonneg _)
  have hsum := Finset.single_le_sum
    (s := Finset.univ) (a := k)
    (f := fun i ↦ (classMultiplicity i : ℝ) *
      ((1 - t) * (b i * Real.log (b i)) + t * (a i * Real.log (a i))) -
      (classMultiplicity i : ℝ) *
        (((1 - t) * b i + t * a i) * Real.log ((1 - t) * b i + t * a i)))
    (fun i _ ↦ sub_nonneg.mpr (hconv i)) (Finset.mem_univ k)
  rw [Finset.sum_sub_distrib] at hsum
  have hupper : (∑ i, (classMultiplicity i : ℝ) *
      ((1 - t) * (b i * Real.log (b i)) + t * (a i * Real.log (a i)))) =
      (1 - t) * (∑ i, (classMultiplicity i : ℝ) * (b i * Real.log (b i))) +
      t * (∑ i, (classMultiplicity i : ℝ) * (a i * Real.log (a i))) := by
    simp only [mul_add, Finset.sum_add_distrib]
    simp_rw [← mul_assoc, mul_comm _ (1 - t), mul_comm _ t, mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  dsimp only at hsum
  rw [hupper, hbk] at hsum
  simp only [mul_zero, zero_add, Real.log_zero] at hsum
  rw [Real.log_mul ht.ne' hak.ne'] at hsum
  nlinarith

/-- An entropy minimizer retains every coordinate that is positive in a feasible profile. -/
theorem solution
    (a b : Fin 10 → ℝ) (ha : InZ a) (hb : InZ b)
    (hba : InY (fun i ↦ b i - a i))
    (hmin : ∀ c : Fin 10 → ℝ, InZ c → InY (fun i ↦ c i - a i) →
      entropyProduct b ≤ entropyProduct c) :
    ∀ k, 0 < a k → 0 < b k := by
  intro k hak
  by_contra hbkpos
  have hbk : b k = 0 := le_antisymm (le_of_not_gt hbkpos) (hb.1 k)
  let D : ℝ := (∑ i, (classMultiplicity i : ℝ) * (a i * Real.log (a i))) -
    ∑ i, (classMultiplicity i : ℝ) * (b i * Real.log (b i))
  let w : ℝ := (classMultiplicity k : ℝ) * a k
  have hw : 0 < w := by
    have hn : 0 < (classMultiplicity k : ℝ) := by
      fin_cases k <;> norm_num [classMultiplicity]
    exact mul_pos hn hak
  let t : ℝ := Real.exp (-((|D| + 1) / w))
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr (by
    exact neg_nonpos.mpr (div_nonneg (by positivity) hw.le))
  have hlog : w * Real.log t = -(|D| + 1) := by
    rw [show Real.log t = -((|D| + 1) / w) from Real.log_exp _]
    field_simp
  let m : Fin 10 → ℝ := fun i ↦ (1 - t) * b i + t * a i
  have hmZ : InZ m := by
    refine ⟨fun i ↦ add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (hb.1 i))
      (mul_nonneg ht.le (ha.1 i)), ?_⟩
    dsimp [m]
    simp_rw [mul_add, ← mul_assoc, mul_comm _ (1 - t), mul_comm _ t, mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hb.2, ha.2]
    ring
  have hmY : InY (fun i ↦ m i - a i) := by
    obtain ⟨s, u, hsu⟩ := hba
    refine ⟨(1 - t) * s, (1 - t) * u, fun i ↦ ?_⟩
    dsimp [m]
    linear_combination (1 - t) * hsu i
  have hbm := hmin m hmZ hmY
  rw [entropyProduct_eq_exp b hb.1, entropyProduct_eq_exp m hmZ.1,
    Real.exp_le_exp] at hbm
  have hbound := entropy_mixture_bound a b ha.1 hb.1 k hak hbk t ht ht1
  have hneg : t * (D + w * Real.log t) < 0 := by
    apply mul_neg_of_pos_of_neg ht
    rw [hlog]
    linarith [le_abs_self D]
  dsimp [D, w] at hneg
  dsimp [m] at hbm
  nlinarith
