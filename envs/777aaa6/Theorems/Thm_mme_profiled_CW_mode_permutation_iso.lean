-- Prove2me | Theorems.Thm_mme_profiled_CW_mode_permutation_iso
-- name    : mme_profiled_CW_mode_permutation_iso
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T15:14:59.041535+00:00
-- url     : https://prove2.me/theorems/9eb5ff4a-c34f-4655-9a15-9578f9bbd69f
-- title:
--   Actual profiled CW5 powers admit cyclic and transposed mode roles
-- statement:
--   For every field, power $N$ and mode profile predicate $P$, let $\sigma$ be either the cyclic permutation or the transposition of the first two modes. Then
--
--   $$\operatorname{CW}_5^N[P\circ\sigma^{-1}]\cong\sigma(\operatorname{CW}_5^N[P]).$$
--
--   These two generators permit all six asymmetric mode roles at any depth of a recursive extraction, including after previous profile projections.
-- source:
--   Constructive tensor-algebra components for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 , Proposition 6.3 and Theorem 6.4. These lemmas implement the finite operations; they do not assert the numerical witness.

import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_six_symmetrized_tau_value
open MME MME.TensorObj MME.ProfiledCW
universe u
set_option autoImplicit false

theorem mme_profiled_CW_mode_permutation_iso {K : Type u} [Field K] {N : ℕ} (P : Predicate N)
    (sigma : Equiv.Perm (Fin 3)) (h : sigma = cyclicPerm ∨ sigma = swapFirstTwoPerm) :
    Isomorphic (tensor K (fun i ↦ P (sigma.symm i))) (permObj sigma (tensor K P)) := by sorry
