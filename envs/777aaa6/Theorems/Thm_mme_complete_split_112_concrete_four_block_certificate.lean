-- Prove2me | Theorems.Thm_mme_complete_split_112_concrete_four_block_certificate
-- name    : mme_complete_split_112_concrete_four_block_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T22:19:16.855732+00:00
-- url     : https://prove2.me/theorems/85d6f608-c648-43b4-974c-df1bfea55d42
-- title:
--   The concrete coupled112 grading has exactly the required four MM blocks
-- statement:
--   Let K be any field and q a nonnegative integer. Fix the explicit standard-coordinate three-grading G of the coupled112 tensor. Every block of G vanishes unless its grade is000,111,012 or102. Its000 and111 blocks are each isomorphic to the matrix-multiplication tensor of dimensions(1,q,1), and its012 and102 blocks are each isomorphic to the tensor of dimensions(q,1,q).
--
--   The grading is the specific published coordinate grading, not an existentially chosen one. Consequently these support and block identifications can be used with the same complete-word labels and lifted basis coordinates as the source router and histogram. Isomorphism has the platform's established meaning of restriction in both directions; the proof supplies actual maps both ways. No asymptotic or scalar value hypothesis occurs.
-- source:
--   Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, J.Symbolic Computation9 (1990), coupled constituent pp266 and270. Reuses the concrete maps in the accepted general-q four-block isomorphism construction, local source research/agents/cw_coupled_core/CoupledThreeGradingSolution.lean, now for the specific public MME.CompleteSplit112.grading and existing DWZCanonical112Coord. Complete-profile consumer: https://arxiv.org/abs/2404.16349v2, Definitions3.4-3.6 and Proposition6.3/Theorem6.4.

import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Definitions.Def_mme_tensor_quotient
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

open MME MME.CompleteSplit112 PiTensorProduct BigOperators DirectSum Module

universe u

theorem mme_complete_split_112_concrete_four_block_certificate
    {K : Type u} [Field K] (q : ℕ) :
    (∀ sigma : Fin 3 → Fin 3,
      sigma ≠ ![0, 0, 0] → sigma ≠ ![1, 1, 1] →
      sigma ≠ ![0, 1, 2] → sigma ≠ ![1, 0, 2] →
        (grading K q).blockTensor sigma = 0) ∧
    TensorObj.Isomorphic (MMObj K 1 q 1)
      ((grading K q).blockSubtensor ![0, 0, 0]) ∧
    TensorObj.Isomorphic (MMObj K 1 q 1)
      ((grading K q).blockSubtensor ![1, 1, 1]) ∧
    TensorObj.Isomorphic (MMObj K q 1 q)
      ((grading K q).blockSubtensor ![0, 1, 2]) ∧
    TensorObj.Isomorphic (MMObj K q 1 q)
      ((grading K q).blockSubtensor ![1, 0, 2]) := by sorry
