-- Prove2me | Theorems.Thm_bernoulli_event_prob_singleton_mem
-- name    : bernoulli_event_prob_singleton_mem
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-26T04:03:19.130584+00:00
-- url     : https://prove2.me/theorems/754b43ce-b23c-4260-ab8d-4b83185f391d
-- statement:
--   Source: Candès--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 18, Section 4.1, equations (4.3)--(4.4).
--
--   Mathematical statement. In the independent Bernoulli observation model on the coordinate set $\operatorname{Fin}(n_1)\times\operatorname{Fin}(n_2)$, every fixed coordinate has marginal inclusion probability $p$:
--
--   $$
--   \operatorname{bernoulliEventProb}\bigl(p,\{\Omega: x\in\Omega\}\bigr)=p.
--   $$
--
--   Variables and notation. The dimensions are $n_1,n_2\in\mathbb N$. The sample set $\Omega\subseteq \operatorname{Fin}(n_1)\times\operatorname{Fin}(n_2)$ is sampled with the Bernoulli product weight from equations (4.3)--(4.4). The parameter $p$ is the Bernoulli inclusion rate, usually $p=m/(n_1n_2)$ in the matrix-completion route. The coordinate $x\in\operatorname{Fin}(n_1)\times\operatorname{Fin}(n_2)$ is fixed. This node does not involve $n=\max(n_1,n_2)$, $\mu_0$, $\mu_1$, or $Z(\Omega)$ except as downstream matrix-completion notation.
--
--   Formalization note. This is a source-derived theorem from the Bernoulli product model, not a new analytic concentration theorem and not an uncited decomposition. It formalizes the singleton marginal implied by Candès--Recht PDF p. 18, Section 4.1, equations (4.3)--(4.4). It is intended as reusable Bernoulli-model bookkeeping for source-backed parents and for local audits of generic Talagrand leaves that require exact one-coordinate event probabilities.
-- source:
--   Candès--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 18, Section 4.1, equations (4.3)--(4.4), where the Bernoulli sample model is defined by independent coordinate indicators with inclusion probability p = m/(n1 n2).

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

open MatrixCompletion
open scoped Classical BigOperators

theorem bernoulli_event_prob_singleton_mem
    {n₁ n₂ : ℕ} (p : ℝ) (x : Fin n₁ × Fin n₂) :
    bernoulliEventProb p (fun Ω : Finset (Fin n₁ × Fin n₂) => x ∈ Ω) = p := by
  sorry
