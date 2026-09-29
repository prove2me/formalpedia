-- Prove2me | Theorems.Thm_mme_tensorAsymptoticRank_kronPow_le_false_at_order_zero
-- name    : mme_tensorAsymptoticRank_kronPow_le_false_at_order_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:33:54.288624+00:00
-- url     : https://prove2.me/theorems/3d583260-d9c5-4cb8-b158-4d6ddf3e3d2b
-- title:
--   Order-zero counterexample to the unrestricted asymptotic-rank power bound
-- statement:
--   The unrestricted Kronecker-power inequality for the concrete asymptotic tensor rank fails at tensor order zero. There exists an order-zero tensor $X$ over $\mathbb Q$ such that
--
--   $$
--   \widetilde R\!\left(X^{\otimes 2}\right)\nleq \widetilde R(X)^2.
--   $$
--
--   This theorem records the boundary-condition obstruction in the concrete rank formalization. The standard matrix-multiplication application has tensor order three and is covered by the corrected theorem under $d\ge2$.
--
--   **Formalization Note** An empty-order Pi tensor product is equivalent to the scalar field. The witness can therefore be represented by the scalar $-1$; the behavior of the natural-number infimum in `tensorRankObj` then distinguishes it from its square.
-- source:
--   Specification audit of Prove2Me theorem d8346a1d-7542-4ff3-95dc-1601f2f96208, based on Definitions.Def_mme_tensor_rank; the intended positive-order asymptotic-rank law is discussed in Wigderson and Zuiddam, Asymptotic spectra: theory, applications and extensions, arXiv:2212.11824.

import Definitions.Def_mme_tensor_rank
open MME
universe u

theorem mme_tensorAsymptoticRank_kronPow_le_false_at_order_zero :
    ∃ X : TensorObj ℚ 0,
      ¬ tensorAsymptoticRank (X.kronPow 2) ≤ tensorAsymptoticRank X ^ 2 := by sorry
