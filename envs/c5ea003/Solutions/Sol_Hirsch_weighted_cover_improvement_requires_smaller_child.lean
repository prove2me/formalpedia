-- Prove2me | solution 1 for Hirsch.weighted_cover_improvement_requires_smaller_child
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-10T23:11:37.745875+00:00
-- url     : https://prove2.me/submissions/65314a03-5c93-470f-8fc9-820209f34901

import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 12000000

-- Source: Solutions/PolynomialFaceCoverBarrier.lean
section

open scoped BigOperators
set_option autoImplicit false

namespace HirschFaceCoverBarrier

/-- A weighted cover cannot improve the vertex-count certificate when every
positive-weight child is itself charged at least its number of vertices.
This is a lower bound on the certificate's cost, not on graph diameter. -/
theorem weighted_cover_cardinality_lower_bound
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (F : ι → Finset V) (B weight : ι → ℕ) (q : ℕ)
    (hcover : ∀ v, q ≤ ∑ i, if v ∈ F i then weight i else 0)
    (hsize : ∀ i, 0 < weight i → (F i).card ≤ B i + 1) :
    q * Fintype.card V ≤ ∑ i, weight i * (B i + 1) := by
  classical
  have hcount :
      (∑ v : V, ∑ i, if v ∈ F i then weight i else 0) =
      ∑ i, weight i * (F i).card := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have hfilter : Finset.univ.filter (fun v => v ∈ F i) = F i := by
      ext v
      simp
    rw [← Finset.sum_filter, hfilter]
    simp [Nat.mul_comm]
  calc
    q * Fintype.card V = ∑ _v : V, q := by simp [Nat.mul_comm]
    _ ≤ ∑ v : V, ∑ i, if v ∈ F i then weight i else 0 := by
      apply Finset.sum_le_sum
      intro v _
      exact hcover v
    _ = ∑ i, weight i * (F i).card := hcount
    _ ≤ ∑ i, weight i * (B i + 1) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : weight i = 0
      · simp [hi]
      · exact Nat.mul_le_mul_left _ (hsize i (Nat.pos_of_ne_zero hi))

/-- Recursive use of the averaging formula preserves the vertex-count
barrier. Arbitrary subface selection and arbitrary integer weights are
allowed. The subtraction is the same truncated natural subtraction as in
the geometric diameter certificate. -/
theorem averaging_budget_ge_card_sub_one
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (F : ι → Finset V) (B weight : ι → ℕ) (q : ℕ) (hq : 0 < q)
    (hcover : ∀ v, q ≤ ∑ i, if v ∈ F i then weight i else 0)
    (hsize : ∀ i, 0 < weight i → (F i).card ≤ B i + 1) :
    Fintype.card V - 1 ≤ (∑ i, weight i * (B i + 1)) / q - 1 := by
  have hcount := weighted_cover_cardinality_lower_bound F B weight q hcover hsize
  have hquot : Fintype.card V ≤ (∑ i, weight i * (B i + 1)) / q := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    simpa only [Nat.mul_comm] using hcount
  omega

/-- A strict improvement from this certificate must use at least one
positive-weight child with an independently better-than-vertex-count bound.
Rank growth and reweighting alone cannot supply that first improvement. -/
theorem improving_certificate_requires_improving_child
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (F : ι → Finset V) (B weight : ι → ℕ) (q : ℕ) (hq : 0 < q)
    (hcover : ∀ v, q ≤ ∑ i, if v ∈ F i then weight i else 0)
    (hsmall : (∑ i, weight i * (B i + 1)) / q - 1 < Fintype.card V - 1) :
    ∃ i, 0 < weight i ∧ B i + 1 < (F i).card := by
  classical
  by_contra hno
  have hsize : ∀ i, 0 < weight i → (F i).card ≤ B i + 1 := by
    intro i hi
    by_contra hbad
    apply hno
    exact ⟨i, hi, by omega⟩
  have hbound := averaging_budget_ge_card_sub_one F B weight q hq hcover hsize
  omega

/-- The purely recursive facet-averaging budget for a cube, when only
singleton terminal bounds are supplied. This is not the cube's diameter. -/
def cubeAveragingBudget : ℕ → ℕ
  | 0 => 0
  | d + 1 => 2 * cubeAveragingBudget d + 1

theorem cubeAveragingBudget_add_one (d : ℕ) : cubeAveragingBudget d + 1 = 2 ^ d := by
  induction d with
  | zero => simp [cubeAveragingBudget]
  | succ d ih =>
    simp only [cubeAveragingBudget, pow_succ]
    omega

theorem cubeAveragingBudget_eq (d : ℕ) : cubeAveragingBudget d = 2 ^ d - 1 := by
  have h := cubeAveragingBudget_add_one d
  omega


end HirschFaceCoverBarrier
end

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

theorem solution {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (F : ι → Finset V) (B weight : ι → ℕ) (q : ℕ) (hq : 0 < q)
    (hcover : ∀ v, q ≤ ∑ i, if v ∈ F i then weight i else 0)
    (hsmall : (∑ i, weight i * (B i + 1)) / q - 1 < Fintype.card V - 1) :
    ∃ i, 0 < weight i ∧ B i + 1 < (F i).card := by
  exact HirschFaceCoverBarrier.improving_certificate_requires_improving_child F B weight q hq hcover hsmall

#print axioms solution
