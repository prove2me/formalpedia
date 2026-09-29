-- Prove2me | solution 1 for mme_profiled_CW_six_mode_permutations_iso
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:25:30.400627+00:00
-- url     : https://prove2.me/submissions/a454a6d0-1cca-4585-a999-7cb8a1a737f1

import Theorems.Thm_mme_profiled_CW_all_mode_permutations_iso
import Theorems.Thm_mme_sixSymmetrization_mode_permutation_iso
import Theorems.Thm_mme_sixSymmetrization_restrict

open MME MME.TensorObj MME.ProfiledCW
universe u

/-- A whole-tensor mode permutation of a CW profile does not change its
six-symmetrized tensor, up to mutual restrictions. -/
theorem solution {K : Type u} [Field K] {N : ℕ}
    (P : Predicate N) (sigma : Equiv.Perm (Fin 3)) :
    Isomorphic (sixSymmetrization (tensor K (fun i => P (sigma.symm i))))
      (sixSymmetrization (tensor K P)) := by
  have h := mme_profiled_CW_all_mode_permutations_iso (K := K) P sigma
  have hs := mme_sixSymmetrization_mode_permutation_iso (tensor K P) sigma
  exact ⟨(mme_sixSymmetrization_restrict h.1).trans hs.1,
    hs.2.trans (mme_sixSymmetrization_restrict h.2)⟩


#print axioms solution
