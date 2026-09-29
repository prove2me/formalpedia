-- Prove2me | solution 1 for mme_CW5_cells_mode_permutation_iso
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:29:39.316273+00:00
-- url     : https://prove2.me/submissions/be4fb1bc-4611-4f0e-9fe9-304d7a4af9d8

import Theorems.Thm_mme_profiled_CW_all_mode_permutations_iso

open MME MME.TensorObj MME.RecursiveYZ MME.CompleteSplit
universe u v w

/-- Reordering the shapes and exact marginals is realized by an isomorphism
of the intact CW5 cell tensors. -/
theorem solution
    (K : Type u) [Field K] {P : Type v} {C : Type w} [Fintype P]
    (ell L : ℕ) (positions : Fin L ≃ P) (cell : P → C)
    (shape : C → Fin 3 → ℕ) (mu : Fin 3 → C → CompleteWord ell → ℕ)
    (sigma : Equiv.Perm (Fin 3)) :
    Isomorphic
      (CWCells.unbroken K 5 ell L positions cell
        (fun c i => shape c (sigma.symm i)) (fun i => mu (sigma.symm i)))
      (permObj sigma (CWCells.unbroken K 5 ell L positions cell shape mu)) := by
  let pred : ProfiledCW.Predicate (L * 2 ^ (ell - 1)) := fun i x =>
    (∀ p, CWCells.grade ((fun r => x (finProdFinEquiv (positions.symm p, r)))) = shape (cell p) i) ∧
      Useful cell (mu i) (fun p r => x (finProdFinEquiv (positions.symm p, r)))
  exact mme_profiled_CW_all_mode_permutations_iso (K := K) pred sigma


#print axioms solution
