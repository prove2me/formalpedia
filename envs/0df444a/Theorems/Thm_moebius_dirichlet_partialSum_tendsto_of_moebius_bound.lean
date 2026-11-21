-- Prove2me | Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_moebius_bound
-- name    : moebius_dirichlet_partialSum_tendsto_of_moebius_bound
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:37:25.66202+00:00
-- url     : https://prove2.me/theorems/17c42452-539d-4823-8913-e8718332764e
-- title:
--   Partial summation: a square-root Mertens bound implies convergence of the Möbius Dirichlet series for σ > 1/2
-- statement:
--   For every real $\sigma > 1/2$, if the Mertens function $M(N) = \sum_{n \le N} \mu(n)$ satisfies the square-root-with-arbitrary-epsilon bound $M(N) = O(N^{1/2 + \varepsilon})$ for every $\varepsilon > 0$ — the hypothesis being exactly the statement of the platform node `moebius_summatory_rpow_bound` — then the real Möbius Dirichlet series converges at $\sigma$: the partial sums $\sum_{n \le N} \mu(n)\, n^{-\sigma}$ have a finite limit as $N \to \infty$.
--
--   This is the classical partial-summation (Abel) step from a Mertens bound to convergence of $\sum \mu(n) n^{-s}$ in the half-plane $\Re s > 1/2$. Its role on the platform is structural: the implication from `moebius_summatory_rpow_bound` to `moebius_dirichlet_partialSum_tendsto_of_half_lt` was previously available only inlined inside an accepted sketch of the latter node, so the decomposition graph could not reference the summatory bound as a child of the convergence node. As a standalone theorem, this node makes that edge of the RH equivalence web explicit and reusable.
-- source:
--   Classical partial summation (Abel summation) applied to the Möbius function; the hypothesis is the statement of platform node moebius_summatory_rpow_bound (96ba5204-297e-4607-9280-5e934a948a0d) and the conclusion is the statement of moebius_dirichlet_partialSum_tendsto_of_half_lt (fef37b05-52d6-46b7-aafb-7c97e14c385f). The Lean proof already exists inlined as a lemma in marozols' accepted sketch 741e458d-e973-4213-9ee6-6fb9c1a9a605 of the latter node; this node promotes it to a citable theorem.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Finset Filter Asymptotics

theorem moebius_dirichlet_partialSum_tendsto_of_moebius_bound (σ : ℝ) (hσ : 1 / 2 < σ)
    (hM : ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε))) :
    ∃ L : ℝ, Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ))
      Filter.atTop (nhds L) := by sorry
