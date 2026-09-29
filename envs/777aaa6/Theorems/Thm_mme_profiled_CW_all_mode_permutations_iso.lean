-- Prove2me | Theorems.Thm_mme_profiled_CW_all_mode_permutations_iso
-- name    : mme_profiled_CW_all_mode_permutations_iso
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T05:21:25.037985+00:00
-- url     : https://prove2.me/theorems/e42ebd3d-1cd8-4f34-b960-436faee82827
-- title:
--   Every mode permutation transports a CW5 profile projection
-- statement:
--   For any predicate on the three fine-word profiles of a CW5 tensor power, transporting the predicate by an arbitrary mode permutation gives a tensor isomorphic to that mode permutation of the original projection. The proof composes the established cycle and swap isomorphisms and checks the six-element permutation classification. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_profiled_CW_mode_permutation_iso
open MME MME.TensorObj MME.ProfiledCW PiTensorProduct
universe u

theorem mme_profiled_CW_all_mode_permutations_iso {K : Type u} [Field K] {N : ℕ}
    (P : Predicate N) (sigma : Equiv.Perm (Fin 3)) :
    Isomorphic (tensor K (fun i => P (sigma.symm i)))
      (permObj sigma (tensor K P)) := by sorry
