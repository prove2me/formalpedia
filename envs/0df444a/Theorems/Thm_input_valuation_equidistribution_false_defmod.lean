-- Prove2me | Theorems.Thm_input_valuation_equidistribution_false_defmod
-- name    : input_valuation_equidistribution_false_defmod
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-13T08:00:45.063327+00:00
-- url     : https://prove2.me/theorems/7cbaa4e8-3697-435d-866b-1d08702f333b
-- title:
--   Valuation-vector equidistribution count is false as stated (shared-definition form)
-- statement:
--   It is false that every positive valuation vector $\bar a$ of length $n_0 \ge 1$ and total sum at most $m$ is realized by exactly $2^{m - |\bar a|}$ odd residues $r < 2^m$. In symbols, the following counting assertion fails: for all such $n_0$, $m$, and $\bar a$,
--
--   $$\#\{r < 2^m : r\ \mathrm{odd},\ \vec{a}^{(n_0)}(r) = \bar a\} = 2^{m-|\bar a|}.$$
--
--   The true count is smaller by a factor of $2$: a valuation vector pins down its input modulo one higher power of $2$ than the formula allows. Pinpointing this factor is a prerequisite for stating the distribution of Syracuse valuations (Tao's Proposition 1.9) correctly.
--
--   **Formalization Note** This is the shared-definition republication of `input_valuation_equidistribution_false`: the helpers are imported from `Definitions.Def_syracuseValuation` instead of being defined in the preamble, whose local definitions break verification. The statement is otherwise unchanged, including the classical decidability instance for the filter.
-- source:
--   Negation of the elementary residue-form equidistribution isolated from Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, arXiv:1909.03562v7, Proposition 1.9 and equation (1.8); original node input_valuation_equidistribution_false by junyihjy. https://arxiv.org/html/1909.03562v7

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_syracuseValuation
attribute [instance] Classical.propDecidable

theorem input_valuation_equidistribution_false_defmod :
    ¬ ∀ n₀ m : ℕ, 1 ≤ n₀ → ∀ ā : Fin n₀ → ℕ, (∀ j, 1 ≤ ā j) →
      Finset.sum Finset.univ (fun j => ā j) ≤ m →
      (Finset.filter (fun r => Odd r ∧ valVec n₀ r = ā) (Finset.range (2 ^ m))).card
        = 2 ^ (m - Finset.sum Finset.univ (fun j => ā j)) := by sorry
