-- Prove2me | Theorems.Thm_bernoulli_event_prob_nonneg
-- name    : bernoulli_event_prob_nonneg
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-24T21:59:20.305631+00:00
-- url     : https://prove2.me/theorems/a3f5c3d1-4115-454b-a176-1420a762ed69
-- statement:
--   Source: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 18, Section 4.1, equations (4.3)--(4.4), where the paper introduces the Bernoulli observation model with independent coordinate indicators.
--
--   Mathematical statement: for an $n_1 \times n_2$ matrix index set and Bernoulli inclusion parameter $p$, define $\Omega \subseteq [n_1]\times[n_2]$ with mass
--   $$
--   w_p(\Omega)=p^{|\Omega|}(1-p)^{n_1n_2-|\Omega|}.
--   $$
--   If $0\le p\le 1$, then every event $E$ has nonnegative Bernoulli event probability
--   $$
--   \mathbb P_p(E)=\sum_\Omega \mathbf 1_E(\Omega) w_p(\Omega) \ge 0.
--   $$
--
--   Notation: here $p$ is the Bernoulli sampling rate from Candes--Recht Section 4.1, $\Omega$ is a finite sampled entry set, and `bernoulliEventProb p Event` is the formal finite sum over all $\Omega$.
--
--   Formalization note: this is a formal bridge, not a new analytic concentration theorem and not a theorem that appears verbatim in the paper. It is a reusable probability-mass sanity lemma for source-backed Bernoulli-model children, whose source-backed parent context is the Bernoulli model in Candes--Recht PDF p. 18, Section 4.1, equations (4.3)--(4.4).
-- source:
--   Candes--Recht, Exact Matrix Completion via Convex Optimization, PDF p. 18, Section 4.1, equations (4.3)--(4.4); formal bridge for the Bernoulli probability mass used by source-backed Bernoulli-model children.

import Definitions.Def_matrix_completion_bernoulli

open MatrixCompletion
open scoped Classical BigOperators

theorem bernoulli_event_prob_nonneg
    {n₁ n₂ : ℕ} {p : ℝ}
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 → 0 ≤ bernoulliEventProb p Event := by
  sorry
