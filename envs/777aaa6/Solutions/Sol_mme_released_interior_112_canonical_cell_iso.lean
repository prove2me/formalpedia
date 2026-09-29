-- Prove2me | solution 1 for mme_released_interior_112_canonical_cell_iso
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:34:57.634391+00:00
-- url     : https://prove2.me/submissions/68a04046-3a84-4e6c-97bb-2f366b7d8fe0

import Theorems.Thm_mme_CW5_cells_mode_permutation_iso
import Definitions.Def_mme_released_interior_integer_profiles
import Mathlib.Tactic.FinCases

open MME MME.TensorObj MME.RecursiveYZ MME.ReleasedInterior MME.CompleteSplit
universe u

/-- The canonical-order child tensor is isomorphic to the corresponding
mode permutation of its physical tensor, at every integer count scale. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1)
    (L m : ℕ) (K : Type u) [Field K] :
    Isomorphic
      (CWCells.unbroken K 5 2 L (Equiv.refl _) (fun _ => Unit.unit)
        (fun _ => ![1, 1, 2])
        (fun i _ w => m * childMarginal owner s r c (Equiv.swap z 2 i) w))
      (permObj (Equiv.swap z 2)
        (CWCells.unbroken K 5 2 L (Equiv.refl _) (fun _ => Unit.unit)
          (fun _ i => (c.val i).val)
          (fun i _ w => m * childMarginal owner s r c i w))) := by
  have hcanon : (fun (_ : Unit) i => (c.val ((Equiv.swap z 2).symm i)).val) =
      fun _ => ![1, 1, 2] := by
    funext a i
    rw [hshape]
    have heq : Equiv.swap z 2 i = z ↔ i = 2 := by
      simpa only [Equiv.swap_apply_right] using
        ((Equiv.swap z 2).injective.eq_iff (a := i) (b := 2))
    simp only [Equiv.symm_swap, heq]
    fin_cases i <;> rfl
  have h := mme_CW5_cells_mode_permutation_iso K 2 L (Equiv.refl _)
    (fun _ => Unit.unit) (fun _ i => (c.val i).val)
    (fun i _ w => m * childMarginal owner s r c i w) (Equiv.swap z 2)
  rw [hcanon] at h
  simpa only [Equiv.symm_swap] using h


#print axioms solution
