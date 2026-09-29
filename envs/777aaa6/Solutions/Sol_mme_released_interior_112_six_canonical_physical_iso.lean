-- Prove2me | solution 1 for mme_released_interior_112_six_canonical_physical_iso
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:48:32.781481+00:00
-- url     : https://prove2.me/submissions/5f29601c-abbe-468b-8156-63caff91040f

import Theorems.Thm_mme_released_interior_112_canonical_cell_iso
import Theorems.Thm_mme_sixSymmetrization_mode_permutation_iso
import Theorems.Thm_mme_sixSymmetrization_restrict

open MME MME.TensorObj MME.RecursiveYZ MME.ReleasedInterior MME.CompleteSplit
universe u

/-- Canonical and physical released 112 child tensors have isomorphic full
symmetrizations, at every integer position and marginal-count scale. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1)
    (L m : ℕ) (K : Type u) [Field K] :
    Isomorphic
      (sixSymmetrization
        (CWCells.unbroken K 5 2 L (Equiv.refl _) (fun _ => Unit.unit)
          (fun _ => ![1, 1, 2])
          (fun i _ w => m * childMarginal owner s r c (Equiv.swap z 2 i) w)))
      (sixSymmetrization
        (CWCells.unbroken K 5 2 L (Equiv.refl _) (fun _ => Unit.unit)
          (fun _ i => (c.val i).val)
          (fun i _ w => m * childMarginal owner s r c i w))) := by
  have h := mme_released_interior_112_canonical_cell_iso owner s r c z hshape L m K
  exact Isomorphic.trans
    ⟨mme_sixSymmetrization_restrict h.1, mme_sixSymmetrization_restrict h.2⟩
    (mme_sixSymmetrization_mode_permutation_iso _ (Equiv.swap z 2))


#print axioms solution
