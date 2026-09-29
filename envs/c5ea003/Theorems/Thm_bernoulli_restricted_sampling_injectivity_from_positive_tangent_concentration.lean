-- Prove2me | Theorems.Thm_bernoulli_restricted_sampling_injectivity_from_positive_tangent_concentration
-- name    : bernoulli_restricted_sampling_injectivity_from_positive_tangent_concentration
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T06:02:18.708295+00:00
-- url     : https://prove2.me/theorems/96a33881-1f5c-4020-af09-11019524019e
-- statement:
--   This is the positive-rate Bernoulli transfer from tangent-space concentration to restricted sampling injectivity.
--
--   Let $S$ be SVD data for a rank-$r$ matrix $Minmathbb R^{n_1	imes n_2}$, and let $Omega$ be sampled in the Bernoulli model with entry probability $p$. The event $mathrm{TangentSamplingConcentration}(Omega,S,p,1/2)$ says that the sampled tangent operator is within a factor $1/2$ of its Bernoulli mean on the tangent space $T$. The event $mathrm{SamplingOperatorInjectiveOnT}(Omega,S)$ says that no nonzero tangent vector is invisible on the observed entries.
--
--   The theorem states that, when $0<ple1$, any lower bound
--
--   $$mathbb P_p{mathrm{TangentSamplingConcentration}(Omega,S,p,1/2)}ge 1-c n^{-eta},qquad n=max(n_1,n_2),$$
--
--   implies the same lower bound for restricted injectivity:
--
--   $$mathbb P_p{mathrm{SamplingOperatorInjectiveOnT}(Omega,S)}ge 1-c n^{-eta}.$$
--
--   The positivity hypothesis $0<p$ is essential. The deprecated zero-rate version is false: for $p=0$, the empty sample can satisfy the concentration inequality vacuously while failing injectivity. This corrected node is proved by the deterministic positive-rate implication plus monotonicity of Bernoulli event probability.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem bernoulli_restricted_sampling_injectivity_from_positive_tangent_concentration
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p c β : ℝ) :
    0 < p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega => TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p (fun Omega => SamplingOperatorInjectiveOnT Omega S) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
