-- Prove2me | Theorems.Thm_mme_dwz_square112_exact_profile_regularity
-- name    : mme_dwz_square112_exact_profile_regularity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T08:05:12.69372+00:00
-- url     : https://prove2.me/theorems/c6325df0-4786-4c9e-8aa4-5b595961d4aa
-- title:
--   Exact square112 profile regularity and cyclic count factorization
-- statement:
--   Consider the four square112 rows $002,011,101,110$. Let nonnegative integer row counts $c_r$ sum to a length $N$, and let $J$ count the exact row words. For mode $i$, let $M_i$ be the full class of mode words with the induced marginal histogram $m_i$, and define
--
--   $
--   F_i=\prod_{a=0}^2\frac{m_i(a)!}{\prod_{r:\operatorname{row}(r)_i=a}c_r!}.
--   $
--
--   Then $J>0$, each mode satisfies $J=|M_i|F_i$, both products below are positive, and
--
--   $
--   J^3=\left(\prod_{i=0}^2|M_i|\right)\left(\prod_{i=0}^2F_i\right).
--   $
--
--   These are exact identities for the concrete word classes, not assumed equicardinality data. They include zero row counts and $N=0$, without equal-corner or balanced-mode restrictions. The result supplies the count normalization for three cyclic copies; the actual cyclic fiber construction, hash isolation, and tensor extraction are separate obligations.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173v5, Section 3: exact type-class/fiber counting and symmetric hashing, printed pp.24–28; restricted T_112 example, Section 6.3, printed p.59. This is an exact finite consequence of the literal four-row marginal/fiber theorem via the sigma-of-fibers equivalence and multinomial positivity, not a claim that a retained family or tensor extraction has already been constructed.

import Definitions.Def_mme_dwz_square112_exact_profile_data
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.SetTheory.Cardinal.Finite

open MME.DWZSquare112
open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_square112_exact_profile_regularity (N : ℕ) (c : Fin 4 → ℕ) (hcount : ∑ r, c r = N) :
    let M : Fin 3 → Type := fun i =>
      {x : Fin N → Fin 3 // ∀ a : Fin 3,
        Fintype.card {j : Fin N // x j = a} = marginal c i a}
    let F : Fin 3 → ℕ := fun i => ∏ a : Fin 3,
      (marginal c i a).factorial /
        ∏ r : {r : Fin 4 // row r i = a}, (c r.1).factorial
    let J := Nat.card (ExactWord N c)
    0 < J ∧
      (∀ i : Fin 3, J = Nat.card (M i) * F i) ∧
      0 < (∏ i : Fin 3, Nat.card (M i)) ∧
      0 < (∏ i : Fin 3, F i) ∧
      J ^ 3 = (∏ i : Fin 3, Nat.card (M i)) * (∏ i : Fin 3, F i) := by sorry
