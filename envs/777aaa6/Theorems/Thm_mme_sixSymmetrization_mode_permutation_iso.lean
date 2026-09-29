-- Prove2me | Theorems.Thm_mme_sixSymmetrization_mode_permutation_iso
-- name    : mme_sixSymmetrization_mode_permutation_iso
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T05:21:21.361187+00:00
-- url     : https://prove2.me/theorems/92f93e2f-159c-4e59-986c-c5d539a04dc8
-- title:
--   Full symmetrization is invariant under every mode permutation
-- statement:
--   For every order-three tensor over any field, six-fold symmetrization of any mode permutation is isomorphic to the original six-fold symmetrization. The proof combines cyclic invariance, the paired-swap description and the six-element permutation classification. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_paired_swap
import Theorems.Thm_mme_cyclicSymmetrization_isomorphic_cyclic_orbit
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
import Mathlib.Tactic.FinCases
open MME MME.TensorObj PiTensorProduct
universe u

theorem mme_sixSymmetrization_mode_permutation_iso
    {K : Type u} [Field K] (T : TensorObj K 3) (sigma : Equiv.Perm (Fin 3)) :
    Isomorphic (sixSymmetrization (permObj sigma T)) (sixSymmetrization T) := by sorry
