-- Prove2me | Theorems.Thm_mme_dwz_square112_exact_profile_marginals_and_fibers
-- name    : mme_dwz_square112_exact_profile_marginals_and_fibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T07:20:21.0333+00:00
-- url     : https://prove2.me/theorems/dd6159c3-48db-456b-9f6e-ebe7d462e681
-- title:
--   Exact marginals and uniform fixed-mode fibers of the four square112 rows
-- statement:
--   Use the four literal square112 fine rows $(0,0,2),(0,1,1),(1,0,1),(1,1,0)$ in the released order, with arbitrary nonnegative integer multiplicities $c_r$. Every exact row word has X counts $(c_0+c_1,c_2+c_3,0)$, Y counts $(c_0+c_2,c_1+c_3,0)$, and Z counts $(c_3,c_1+c_2,c_0)$. Write $m_i(a)$ for these mode-$i$ marginal counts. For every mode word $x$ with this exact histogram,
--
--   $$\#\{w:\operatorname{mode}_i(w)=x\}=\prod_{a=0}^2\frac{m_i(a)!}{\prod_{r:\operatorname{row}(r)_i=a}c_r!},$$
--
--   where $w$ ranges over the actual length-$N$ row words with the four prescribed multiplicities. Thus the fiber size is independent of the ordering of $x$, not merely constant over projections assumed in advance to have a nonempty fiber. Zero counts and length zero are included; no equal-corner, balanced-X/Y or modern balanced-family range premise occurs. This is a concrete uniform-degree input for the three-cyclic symmetric hashing construction. It asserts neither a retained hash family nor tensor extraction or a scalar value bound.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173v5, Lemma 3.6 and Section 3.10 (printed pp. 22, 24–27), Definition 3.9 and Section 6.3 (printed pp. 23–24, 59). Literal released square112 support order checked in power4_dup_2.371919.mat, SHA-256 2aa5713eb352bc94c939d340743c4107b42d274c9fa2058ff879cd7603142aeb. The proof reuses the Proved generic mme_fintype_constrained_prescribed_fiber_function_card, already used in prior Stothers phi134 fiber enumeration. This is a derived finite combinatorial interface, not a claim that the full symmetric extraction or DWZ value has been proved.

import Definitions.Def_mme_dwz_square112_exact_profile_data
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.SetTheory.Cardinal.Finite

open MME.DWZSquare112
open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_square112_exact_profile_marginals_and_fibers (N : ℕ) (c : Fin 4 → ℕ) :
    (∀ (w : ExactWord N c) (i a : Fin 3),
      Fintype.card {j : Fin N // modeWord w i j = a} = marginal c i a) ∧
    ∀ (i : Fin 3) (x : Fin N → Fin 3),
      (∀ a : Fin 3, Fintype.card {j : Fin N // x j = a} = marginal c i a) →
      Nat.card {v : ExactWord N c // modeWord v i = x} =
        ∏ a : Fin 3,
          (marginal c i a).factorial /
            ∏ r : {r : Fin 4 // row r i = a}, (c r.1).factorial := by sorry
