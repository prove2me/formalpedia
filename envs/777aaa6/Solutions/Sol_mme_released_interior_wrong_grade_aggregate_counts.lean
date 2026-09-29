-- Prove2me | solution 1 for mme_released_interior_wrong_grade_aggregate_counts
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:18:39.899021+00:00
-- url     : https://prove2.me/submissions/dd2a7a6a-d679-4832-871a-5e6719c9020f

import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_released_global_profile_data
import Definitions.Def_mme_more_asymmetry_released_exact_profile_seed
import Mathlib.Data.List.Sort

set_option autoImplicit false
namespace MME.ReleasedInterior
open MoreAsymmetryExactSeed




open BigOperators MME.RecursiveYZ MME.CompleteSplit
private theorem inverse_role_apply : ∀ (owner : Fin 6) (i : Fin 3),
    inverseRole owner (role owner i) = i := by decide +kernel



private theorem child_mem_grade (t : Term) (j : ℕ) (shape : List ℕ)
    (p : ℕ × ℕ) (hp : p ∈ child t j shape) :
    List.ofFn (fun i : Fin 3 =>
      (ReleasedGlobal.elementary ⟨p.1 % 6, Nat.mod_lt _ (by decide)⟩ i).val +
      (ReleasedGlobal.elementary ⟨p.1 / 6 % 6, Nat.mod_lt _ (by decide)⟩ i).val) = shape := by
  obtain ⟨a, ha, heq⟩ := List.mem_map.mp hp
  have hfst : a = p.1 := congrArg Prod.fst heq
  have hgrade := (List.mem_filter.mp ha).2
  simpa only [hfst, beq_iff_eq] using hgrade

private theorem child_word_grade (owner : Fin 6) (s : Fin 45) (r : Fin 6)
    (c : Split s) (p : ℕ × ℕ)
    (hp : p ∈ child (seed owner s) r.val (sourceShape owner c)) (i : Fin 3) :
    ∑ h, (childWord owner p.1 i h).val = (c.val i).val := by
  have h := child_mem_grade _ _ _ p hp
  unfold sourceShape at h
  have hvec := List.ofFn_injective h
  have hi := congrFun hvec (role owner i)
  change (∑ h : Fin 2, (childWord owner p.1 i h).val) = (c.val i).val
  rw [Fin.sum_univ_two]
  simpa only [inverse_role_apply, childWord,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, Nat.div_one] using hi


private theorem global_row_support : ∀ (owner : Fin 6) (s : Fin 45),
    (ReleasedGlobal.jointRows owner s).all (fun a => decide
      (∀ i : Fin 3, (∑ h, (ReleasedGlobal.atom a.1 i h).val) = parent s 0 i)) = true := by
  decide +kernel

private theorem child_marginal_eq_zero (owner : Fin 6) (s : Fin 45) (r : Fin 6)
    (c : Split s) (i : Fin 3) (w : CompleteWord 2)
    (hw : (∑ h, (w h).val) ≠ (c.val i).val) :
    childMarginal owner s r c i w = 0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  have hne : childWord owner a.1 i ≠ w := by
    intro heq
    exact hw (heq ▸ child_word_grade owner s r c a ha i)
  simp only [if_neg hne]

private theorem grade_split_three (w : CompleteWord 3) :
    (∑ q, (w q).val) =
      (∑ q, ((completeWordSplitEquiv 2 (by decide) w).1 q).val) +
      (∑ q, ((completeWordSplitEquiv 2 (by decide) w).2 q).val) := by
  simp [Fin.sum_univ_succ, completeWordSplitEquiv, fineWordSplitEquiv]
  omega

end MME.ReleasedInterior
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

/-- Words outside the actual parent grade have no contribution on either side
of the aggregate marginal identity. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (i : Fin 3) (w : CompleteWord 3)
    (hw : (∑ h, (w h).val) ≠ parent s 0 i) :
    ((ReleasedGlobal.jointRows owner s).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed owner s).region.getD r.val 0 *
      ∑ c : Split s, splitWeight owner s r c *
        childMarginal owner s r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal owner s r (complement (parent_total s r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  have hleft : ((ReleasedGlobal.jointRows owner s).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    have hsupport := global_row_support owner s
    rw [List.all_eq_true] at hsupport
    have hgrade := (of_decide_eq_true (hsupport a ha)) i
    have hne : ReleasedGlobal.atom a.1 i ≠ w := by
      intro heq
      exact hw (heq ▸ hgrade)
    simp only [if_neg hne]
  rw [hleft]
  symm
  apply Finset.sum_eq_zero
  intro r _
  suffices hz : (∑ c : Split s, splitWeight owner s r c *
      childMarginal owner s r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
      childMarginal owner s r (complement (parent_total s r) c) i
        ((completeWordSplitEquiv 2 (by decide)) w).2) = 0 by rw [hz, mul_zero]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hl : (∑ q, ((completeWordSplitEquiv 2 (by decide) w).1 q).val) = (c.val i).val
  · have hr : (∑ q, ((completeWordSplitEquiv 2 (by decide) w).2 q).val) ≠
        ((complement (parent_total s r) c).val i).val := by
      intro hright
      apply hw
      rw [grade_split_three, hl, hright]
      change (c.val i).val + (parent s r i - (c.val i).val) = parent s 0 i
      have hle := c.property.2 i
      exact Nat.add_sub_of_le hle
    have hz := child_marginal_eq_zero owner s r
      (complement (parent_total s r) c) i _ hr
    simp only [parent, RecursiveYZ.complement] at hz ⊢
    rw [hz, mul_zero]
  · rw [child_marginal_eq_zero owner s r c i _ hl, mul_zero, zero_mul]

#print axioms solution
