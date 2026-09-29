-- Prove2me | solution 1 for mme_released_interior_empty_cell_six_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:48:34.652711+00:00
-- url     : https://prove2.me/submissions/823f9d06-e864-470f-8518-236b2d3b63bb

import Theorems.Thm_mme_CW_empty_cell_six_extraction
import Theorems.Thm_mme_released_interior_child_scale_identities

open MME MME.TensorObj MME.RecursiveYZ MME.ReleasedInterior
  MME.MoreAsymmetryExactSeed MME.CompleteSplit
universe u

/-- A released child of zero combined weight contributes a scalar matrix
tensor at every physical replication scale, regardless of its shape. -/
theorem solution
    {K : Type u} [Field K] (owner : Fin 6) (s : Fin 45) (r : Fin 6)
    (c : Split s) (k : ℕ)
    (hweight : (seed owner s).region.getD r.val 0 *
      (splitWeight owner s r c +
        splitWeight owner s r (complement (parent_total s r) c)) = 0) :
    Restrict (MMObj K 1 1 1)
      (sixSymmetrization
        (CWCells.unbroken K 5 2
          ((2 * k) * (splitCount owner s r c +
            splitCount owner s r (complement (parent_total s r) c))) (Equiv.refl _)
          (fun _ => Unit.unit) (fun _ i => (c.val i).val)
          (fun i _ w => (2 * k) * integerProfile owner s i ⟨r, c⟩ w))) := by
  obtain ⟨hlength, hprofile⟩ := mme_released_interior_child_scale_identities owner s r c k
  simp only [hweight, Nat.zero_mul, Nat.mul_zero] at hlength hprofile
  have htensor := congrArg (fun n : ℕ => sixSymmetrization
    (CWCells.unbroken K 5 2 n (Equiv.refl _)
      (fun _ => Unit.unit) (fun _ i => (c.val i).val)
      (fun i _ w => (2 * k) * integerProfile owner s i ⟨r, c⟩ w))) hlength
  apply (congrArg (fun T => Restrict (MMObj K 1 1 1) T) htensor).mp
  simpa only [← hprofile] using
    (mme_CW_empty_cell_six_extraction (K := K) 5 2 (fun i => (c.val i).val))


#print axioms solution
