-- Prove2me | Theorems.Thm_bernoulli_expectation_centered_singleton_indicator_scaled_eq_zero
-- name    : bernoulli_expectation_centered_singleton_indicator_scaled_eq_zero
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-26T04:35:32.301592+00:00
-- url     : https://prove2.me/theorems/f10ac2cb-6d97-4f6c-a269-3034a922c7bf
-- statement:
--   Source: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 18, Section 4.1, equations (4.3)--(4.4).
--
--   Mathematical statement: in the Bernoulli sampling model from equations (4.3)--(4.4), each matrix coordinate is included independently with probability $p$. For fixed dimensions $n_1,n_2$, a fixed coordinate $x \in [n_1]\times[n_2]$, and a scalar amplitude $A\in\mathbb R$, the centered singleton indicator has zero Bernoulli expectation after scaling:
--
--   $$
--   \mathbb E_{\Omega}\left[((\mathbf 1_{x\in\Omega}-p)A)\right]=0.
--   $$
--
--   Notation: $\Omega\subseteq [n_1]\times[n_2]$ is the Bernoulli sample set, $p$ is the coordinate inclusion probability from the paper, $n=\max(n_1,n_2)$ is the matrix-size convention used in the mission even though this local identity does not depend on $n$, and $A$ is an arbitrary real scale. The quantities $\mu_0$, $\mu_1$, $Z(\Omega)$, and `successProb` do not enter this elementary Bernoulli marginal identity.
--
--   Formalization note: this is a source-derived theorem, not a theorem stated verbatim in Candes--Recht. It formalizes the one-coordinate centered expectation consequence of the Bernoulli product model in PDF p. 18, Section 4.1, equations (4.3)--(4.4), and can be used as a reusable local support lemma for source-backed Talagrand or counterexample audits.
-- source:
--   Candes--Recht, Exact Matrix Completion via Convex Optimization, PDF p. 18, Section 4.1, equations (4.3)--(4.4).

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

open MatrixCompletion
open scoped Classical BigOperators

theorem bernoulli_expectation_centered_singleton_indicator_scaled_eq_zero
    {n₁ n₂ : ℕ} (p A : ℝ) (x : Fin n₁ × Fin n₂) :
    bernoulliExpectation p
        (fun Ω : Finset (Fin n₁ × Fin n₂) =>
          (((if x ∈ Ω then (1 : ℝ) else 0) - p) * A)) = 0 := by
  sorry
