-- Prove2me | solution 1 for mme_intact_reference_restrict_profiled_output
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T01:42:55.014638+00:00
-- url     : https://prove2.me/submissions/95b1f4d6-c9c8-49e8-8f97-eb9b50b8f6ed

import Definitions.Def_mme_recursive_profiled_CW_data
import Theorems.Thm_mme_basis_projected_family_restrict

open MME MME.TensorObj MME.ProfiledCW MME.RecursiveYZ
open MME.RecursiveYZ.CWCells MME.CompleteSplit
set_option autoImplicit false
universe u

private theorem tensor_cast {K : Type u} [Field K] {n m : ℕ} (h : n = m)
    (P : Predicate m) :
    tensor K (fun i (x : FineWord n) ↦ P i (fun j ↦ x (Fin.cast h.symm j))) =
      tensor K P := by
  subst m
  rfl

private theorem split_cast {S : Type} {ell L N : ℕ} (p : Fin L ≃ S)
    (h : L * 2 ^ (ell - 1) = N) (x : WordIndex.{u} 5 ell L) :
    split p h (fun j ↦ fine x (Fin.cast h.symm j)) = CWCells.label 5 ell L p x := by
  funext s r
  simp [split, CWCells.label, fine]

/-- The intact reference tensor is contained in the profiled tensor of its
exact graded and useful output words, in the chosen flat coordinates. -/
theorem solution
    {K : Type u} [Field K] {half R ell L N : ℕ}
    {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (reference : Address half R parent n) (positions : Fin L ≃ Position n)
    (length : L * 2 ^ (ell - 1) = N)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ) :
    Restrict
      (unbroken K 5 ell L positions (fullCell htotal reference)
        (fun cell i ↦ (cell.2.val i).val) mu)
      (tensor K (fun i x ↦ Graded htotal i reference (split positions length x) ∧
        Useful (fullCell htotal reference) (mu i) (split positions length x))) := by
  classical
  let P : Predicate N := fun i x ↦ Graded htotal i reference (split positions length x) ∧
    Useful (fullCell htotal reference) (mu i) (split positions length x)
  let pull : Predicate (L * 2 ^ (ell - 1)) :=
    fun i x ↦ P i (fun j ↦ x (Fin.cast length.symm j))
  have hmono : Restrict
      (unbroken K 5 ell L positions (fullCell htotal reference)
        (fun cell i ↦ (cell.2.val i).val) mu)
      (tensor K pull) := by
    apply mme_basis_projected_family_restrict (CWCells.source K 5 ell L)
      (CWCells.basis K 5 ell L) (fun i x ↦ pull i (fine x))
      (fun (_ : Fin 1) ↦ allowed 5 ell L positions (fullCell htotal reference)
        (fun cell i ↦ (cell.2.val i).val) mu)
    · intro j i x hx
      dsimp only [pull, P]
      rw [split_cast]
      exact hx
    · intro x js _ _
      exact ⟨0, funext (fun i ↦ Fin.eq_zero (js i))⟩
  rw [show tensor K pull = tensor K P from tensor_cast length P] at hmono
  exact hmono


#print axioms solution
