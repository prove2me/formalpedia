-- Prove2me | Theorems.Thm_scalar_centered_sampling_markov_tail_from_qmoment_bound
-- name    : scalar_centered_sampling_markov_tail_from_qmoment_bound
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T20:07:45.671999+00:00
-- url     : https://prove2.me/theorems/7e04c4ca-8086-4187-ac5a-12962a5dd1ed
-- statement:
--   **Markov's inequality on the finite Bernoulli observation measure.** Fix entry dimensions $n_1,n_2$ and an inclusion probability $p\in[0,1]$, giving the product Bernoulli measure on subsets $\Omega$ of the $n_1n_2$ matrix entries (each entry included independently with probability $p$). Let $Z(\Omega)$ be any real-valued statistic of the observation set, let $q\ge 1$ be an integer, $t>0$ a threshold, and $\mathrm{failProb}\ge 0$. If the $q$-th absolute moment is controlled, $$\mathbb{E}\,|Z|^q \le t^q\cdot \mathrm{failProb},$$ then $Z$ stays within the threshold with high probability: $$\mathbb{P}\big(|Z(\Omega)|\le t\big)\ \ge\ 1-\mathrm{failProb}.$$ This is the standard $q$-th moment Markov bound, here proved directly on the explicit powerset-sum Bernoulli measure: the weights $p^{|\Omega|}(1-p)^{n_1n_2-|\Omega|}$ are nonnegative and sum to $1$ (binomial theorem), and on the bad event $\{|Z|>t\}$ one has $t^q<|Z|^q$, so $t^q\,\mathbb P(|Z|>t)\le \mathbb E|Z|^q\le t^q\,\mathrm{failProb}$. It is the reusable concentration core for the scalar centered-sampling Bernstein tails (the analogue, for the scalar statistic $\mathrm{matrixEntrySum}$ of a centered sampling fluctuation, of the proved spectral-norm Markov tail).
-- source:
--   Candès–Recht, Exact Matrix Completion via Convex Optimization, arXiv:0805.4471 (Markov / q-th moment method used in §4–6); standard Markov inequality.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators Classical

theorem scalar_centered_sampling_markov_tail_from_qmoment_bound {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (Z : Finset (Fin n₁ × Fin n₂) → ℝ) (q : ℕ) (hq : 1 ≤ q) (t failProb : ℝ) (ht : 0 < t) (hfail : 0 ≤ failProb) (hmoment : bernoulliExpectation p (fun Omega => |Z Omega| ^ q) ≤ t ^ q * failProb) : bernoulliEventProb p (fun Omega => |Z Omega| ≤ t) ≥ 1 - failProb := by sorry
