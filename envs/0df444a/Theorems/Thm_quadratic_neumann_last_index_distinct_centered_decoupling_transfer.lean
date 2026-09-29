-- Prove2me | Theorems.Thm_quadratic_neumann_last_index_distinct_centered_decoupling_transfer
-- name    : quadratic_neumann_last_index_distinct_centered_decoupling_transfer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T01:05:50.856046+00:00
-- url     : https://prove2.me/theorems/f81d8e71-ed0b-4ce0-b9fe-4c7f1add61c6
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Two-variable decoupling transfer for the centered $\omega_{1} = \omega_{2} \ne \omega_{3}$ quadratic contribution: a high-probability estimate in the two-copy Bernoulli model implies the corresponding one-copy estimate, with only universal constant loss.
--
--   Lecture-note formulation:
--
--   $$
--   \mathbb P_{p,p}(\|Q_{1=2\ne3}(\Omega_1,\Omega_2)\|\le a)\ge 1-\varepsilon
--   \quad\Longrightarrow\quad
--   \mathbb P_p(\|Q_{1=2\ne3}(\Omega,\Omega)\|\le C a)\ge 1-C\varepsilon.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 2 subclaims: quadratic Neumann last index distinct centered pair decoupling tail bound; quadratic Neumann last index distinct centered original tail from diagonal decoupled tail.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_last_index_distinct_centered_decoupling_transfer :
    ∃ Cdecouple cdecouple : ℝ, 0 < Cdecouple ∧ 0 < cdecouple ∧
      ∀ {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
        (S : SVD M r) (p Cdec cdec β lam : ℝ),
        0 ≤ p → p ≤ 1 → 0 < Cdec → 0 < cdec →
        bernoulliPairEventProb p
            (fun Omega1 Omega3 =>
              spectralNorm
                (quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
                  Omega1 Omega3 S p) ≤
                Cdec * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - cdec * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm
                (quadraticNeumannLastIndexDistinctCenteredContribution Omega S p) ≤
                (Cdecouple * Cdec) * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - (cdecouple * cdec) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
