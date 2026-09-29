-- Prove2me | Definitions.Def_mme_recursive_split_coordinate_data
-- name    : mme_recursive_split_coordinate_data
-- status  : Definition
-- author  : @Robertboy18
-- created : 2026-09-23T09:38:04.507429+00:00
-- url     : https://prove2.me/theorems/32eccf23-63fb-4a3d-9aa0-f26ffb31d3f1
-- title:
--   Coordinate permutations of recursive splits
-- statement:
--   A coordinate permutation transports admissible recursive splits and preserves their total grade.

import Definitions.Def_mme_recursive_yz_owned_filters
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace MME.RecursiveThinSplit

/-- Relabel the three modes of a recursive split, including its parent grades. -/
def coordinateEquiv {half : ℕ} (parent : Fin 3 → ℕ) (p : Equiv.Perm (Fin 3)) :
    Split half parent ≃ Split half (fun i => parent (p i)) where
  toFun c := ⟨fun i => c.val (p i), by
    constructor
    · have h := Equiv.sum_comp p (fun i => (c.val i).val)
      simp only [Fin.sum_univ_three] at h
      exact h.trans c.property.1
    · exact fun i => c.property.2 (p i)⟩
  invFun c := ⟨fun i => c.val (p.symm i), by
    constructor
    · have h := Equiv.sum_comp p.symm (fun i => (c.val i).val)
      simp only [Fin.sum_univ_three] at h
      exact h.trans c.property.1
    · intro i
      simpa using c.property.2 (p.symm i)⟩
  left_inv c := by
    apply Subtype.ext
    funext i
    exact congrArg c.val (p.apply_symm_apply i)
  right_inv c := by
    apply Subtype.ext
    funext i
    exact congrArg c.val (p.symm_apply_apply i)

@[simp] theorem coordinateEquiv_apply {half : ℕ} (parent : Fin 3 → ℕ)
    (p : Equiv.Perm (Fin 3)) (c : Split half parent) (i : Fin 3) :
    (coordinateEquiv parent p c).val i = c.val (p i) := rfl

@[simp] theorem coordinateEquiv_symm_apply {half : ℕ} (parent : Fin 3 → ℕ)
    (p : Equiv.Perm (Fin 3)) (c : Split half (fun i => parent (p i))) (i : Fin 3) :
    ((coordinateEquiv parent p).symm c).val i = c.val (p.symm i) := rfl

/-- The parent total is unchanged by a mode permutation. -/
theorem coordinate_total {half : ℕ} {parent : Fin 3 → ℕ}
    (h : parent 0 + parent 1 + parent 2 = 2 * half) (p : Equiv.Perm (Fin 3)) :
    parent (p 0) + parent (p 1) + parent (p 2) = 2 * half := by
  have hs := Equiv.sum_comp p parent
  simp only [Fin.sum_univ_three] at hs
  exact hs.trans h

end MME.RecursiveThinSplit


