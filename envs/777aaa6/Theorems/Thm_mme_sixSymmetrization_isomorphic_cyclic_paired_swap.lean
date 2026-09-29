-- Prove2me | Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_paired_swap
-- name    : mme_sixSymmetrization_isomorphic_cyclic_paired_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:14:40.419719+00:00
-- url     : https://prove2.me/theorems/137f269c-6c5e-49b4-948e-ce75dfafae87
-- title:
--   Six-symmetrization as cyclic symmetrization of a swapped pair
-- statement:
--   For every order-three tensor $T$, its full six-symmetrization is isomorphic to the cyclic symmetrization of the paired tensor $T \otimes s(T)$, where $s$ swaps the first two modes:
--
--   $$\operatorname{Sym}_6(T) \cong \operatorname{Sym}_3(T \otimes s(T)).$$
--
--   This identity regroups the six mode permutations into three pairs. It is especially useful when a construction concatenates data from an orientation and its swapped copy before applying cyclic assembly.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.3; elementary dihedral regrouping of the six mode permutations.

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge

open MME

universe u

set_option autoImplicit false

theorem mme_sixSymmetrization_isomorphic_cyclic_paired_swap
    {K : Type u} [Field K] (T : TensorObj K 3) :
    TensorObj.Isomorphic
      (sixSymmetrization T)
      (cyclicSymmetrization
        (TensorObj.kron T (TensorObj.permObj swapFirstTwoPerm T))) := by
  sorry
