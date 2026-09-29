-- Prove2me | Theorems.Thm_bernoulli_five_event_intersection_probability_from_lower_bounds
-- name    : bernoulli_five_event_intersection_probability_from_lower_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:04:39.689711+00:00
-- url     : https://prove2.me/theorems/47290353-c9cd-4aa6-b230-fe5530d01c84
-- statement:
--   Role. It is a reusable node in the Candes-Recht decomposition, phrased as a standalone theorem so that downstream sketches can import it directly.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Five-event finite Bernoulli union bound in lower-bound form.
--
--   Lecture-note formulation:
--
--   $$
--   \mathbb P(E_i)\ge 1-\varepsilon_i\ \text{ for every }i
--   \quad\Longrightarrow\quad
--   \mathbb P\!\left(\bigcap_i E_i\right)\ge 1-\sum_i\varepsilon_i.
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

theorem bernoulli_five_event_intersection_probability_from_lower_bounds
    {n₁ n₂ : ℕ} (p cA cB cC cD cE failureScale : ℝ)
    (EventA EventB EventC EventD EventE :
      Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    bernoulliEventProb p EventA ≥ 1 - cA * failureScale →
    bernoulliEventProb p EventB ≥ 1 - cB * failureScale →
    bernoulliEventProb p EventC ≥ 1 - cC * failureScale →
    bernoulliEventProb p EventD ≥ 1 - cD * failureScale →
    bernoulliEventProb p EventE ≥ 1 - cE * failureScale →
    bernoulliEventProb p
        (fun Omega =>
          EventA Omega ∧ EventB Omega ∧ EventC Omega ∧ EventD Omega ∧
            EventE Omega) ≥
      1 - ((((cA + cB) + cC) + cD) + cE) * failureScale := by
  sorry
