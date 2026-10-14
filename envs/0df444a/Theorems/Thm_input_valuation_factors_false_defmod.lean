-- Prove2me | Theorems.Thm_input_valuation_factors_false_defmod
-- name    : input_valuation_factors_false_defmod
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-13T08:00:41.621821+00:00
-- url     : https://prove2.me/theorems/00895691-f444-4a1f-bf4c-e7f6973f60f2
-- title:
--   Valuation vector is not determined by the residue mod $2^m$ (shared-definition form)
-- statement:
--   It is false that the Syracuse valuation vector of an odd integer $n$ is always determined by the residue $n \bmod 2^m$ whenever the valuation sum is at most $m$. In symbols, the following assertion fails: for all lengths $n_0$, all odd $n$, and all $m$ with valuation sum at most $m$,
--
--   $$\vec{a}^{(n_0)}(n) = \vec{a}^{(n_0)}(n \bmod 2^m).$$
--
--   The residue retains only the lowest $m$ bits of $n$, but the valuation $\nu_2(3n+1)$ can depend on the next bit, so the claimed factoring through the residue loses information. Recording exactly where this naive factoring fails delimits what a correct proof of Tao's Proposition 1.9 must pay for (an extra bit of precision).
--
--   **Formalization Note** This is the shared-definition republication of `input_valuation_factors_false`: the helpers `syrVal`, `valVec`, `valSum` are imported from `Definitions.Def_syracuseValuation` instead of being defined in the preamble, whose local definitions break verification. The statement is otherwise unchanged.
-- source:
--   Negation of the factoring clause isolated from Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, arXiv:1909.03562v7, Proposition 1.9 and equation (1.8); original node input_valuation_factors_false by junyihjy. https://arxiv.org/html/1909.03562v7

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_syracuseValuation

theorem input_valuation_factors_false_defmod :
    ¬ ∀ n₀ n m : ℕ, Odd n → valSum n₀ n ≤ m →
      valVec n₀ n = valVec n₀ (n % 2 ^ m) := by sorry
