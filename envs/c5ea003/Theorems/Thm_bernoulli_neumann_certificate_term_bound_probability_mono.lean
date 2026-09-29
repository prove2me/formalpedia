-- Prove2me | Theorems.Thm_bernoulli_neumann_certificate_term_bound_probability_mono
-- name    : bernoulli_neumann_certificate_term_bound_probability_mono
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:06:52.772152+00:00
-- url     : https://prove2.me/theorems/f7c67212-c593-43e4-8402-6e60a9f4756e
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Monotonicity of Bernoulli probability for Neumann certificate term bounds: a smaller spectral-norm threshold implies any larger threshold.
--
--   Lecture-note formulation:
--
--   $$
--   E_{\mathrm{strong}}\subseteq E_{\mathrm{weak}}
--   \quad\Longrightarrow\quad
--   \mathbb P_p(E_{\mathrm{weak}})\ge \mathbb P_p(E_{\mathrm{strong}})
--   \quad\text{for the Neumann certificate event}.
--   $$
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 2 subclaims: Bernoulli event probability mono; Neumann certificate term spectral bound mono.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem bernoulli_neumann_certificate_term_bound_probability_mono
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p : ℝ) (k : ℕ) (small large c β : ℝ) :
    0 ≤ p → p ≤ 1 →
    small ≤ large →
    bernoulliEventProb p
        (fun Omega => NeumannCertificateTermSpectralBound Omega S p k small) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => NeumannCertificateTermSpectralBound Omega S p k large) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
