-- Prove2me | Theorems.Thm_ordered_dirichlet_convergence_implies_little_o_partial_sums
-- name    : ordered_dirichlet_convergence_implies_little_o_partial_sums
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-05T04:51:37.596806+00:00
-- url     : https://prove2.me/theorems/6fecab04-83a7-4dc7-8c7c-863636c9098d
-- title:
--   Ordered Dirichlet convergence forces little-o cancellation at the same exponent
-- statement:
--   Let $f:\mathbb N\to\mathbb C$ and $\sigma>0$. If the ordered partial sums $\sum_{n=1}^N f(n)n^{-\sigma}$ converge to a finite complex limit, then
--
--   $$\sum_{n=1}^Nf(n)=o(N^\sigma).$$
--
--   The conclusion is little-o at the same exponent, which is stronger than merely $O(N^\sigma)$. This is a Dirichlet-series specialization of Kronecker's lemma and requires neither absolute convergence nor positivity of the coefficients. It does not supply the assumed convergence for the Moebius series.
-- source:
--   Kronecker's lemma, derived here using discrete Abel summation. Pinned Mathlib https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/BigOperators/Module.lean#L57, Finset.sum_range_by_parts, and https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Asymptotics/Lemmas.lean#L407, isLittleO_const_left. The proof includes a general monotone-weight Kronecker lemma and then specializes to the weight n^sigma; the exact specialized statement is not attributed verbatim to Mathlib.

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.NormNum
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic.FieldSimp
open MeasureTheory
open scoped Topology

theorem ordered_dirichlet_convergence_implies_little_o_partial_sums
    (f : ℕ → ℂ) {σ : ℝ} (hσ : 0 < σ) {L : ℂ}
    (hlim : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ) ^ (σ : ℂ))
      Filter.atTop (nhds L)) :
    Asymptotics.IsLittleO Filter.atTop
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n)
      (fun N : ℕ => (N : ℝ) ^ σ) := by sorry
