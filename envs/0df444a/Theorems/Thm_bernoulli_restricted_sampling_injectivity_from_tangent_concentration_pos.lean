-- Prove2me | Theorems.Thm_bernoulli_restricted_sampling_injectivity_from_tangent_concentration_pos
-- name    : bernoulli_restricted_sampling_injectivity_from_tangent_concentration_pos
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-21T18:19:10.903369+00:00
-- url     : https://prove2.me/theorems/29b6f5ea-da02-4ee8-8398-e89246f51788
-- statement:
--   POSITIVE-p CORRECTION of the disproved node `bernoulli_restricted_sampling_injectivity_from_tangent_concentration`. With the inclusion probability hypothesis strengthened to $0<p$ (the original allowed $p=0$, where it is false: take $\Omega=\varnothing$, then tangent concentration holds vacuously but $P_\Omega$ is the zero map and hence not injective on a nontrivial tangent space). Claim: if $0<p\le 1$ and the high-probability tangent-concentration event $\{\,\|p^{-1}P_TP_\Omega P_T-P_T\|_{T\to T}\le 1/2\,\}$ has Bernoulli probability $\ge 1-c\,n^{-\beta}$, then the event that the sampling operator $P_\Omega$ is injective on the tangent space $T$ also has probability $\ge 1-c\,n^{-\beta}$. Pointwise, concentration at scale $1/2$ gives $(p/2)\|H\|_F\le\|P_TP_\Omega P_T H\|_F$ for $H\in T$, so $P_\Omega H=0\Rightarrow H=0$; the Bernoulli statement then follows by monotonicity of $\mathrm{bernoulliEventProb}$ under event inclusion ($0\le p\le 1$ makes all observation weights nonnegative). Source: Candès–Recht 2009 (arXiv:0805.4471), §4.2 "The injectivity property", Theorem 4.1 eq. (4.5) and the well-conditioning conclusion after eq. (4.11), p.19–20.
-- source:
--   Candes, Emmanuel J., and Benjamin Recht. "Exact matrix completion via convex optimization." arXiv:0805.4471 (2009), §4.2, Theorem 4.1 eq. (4.5)/(4.11), p.19-20.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem bernoulli_restricted_sampling_injectivity_from_tangent_concentration_pos
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p c β : ℝ) :
    0 < p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega => TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p (fun Omega => SamplingOperatorInjectiveOnT Omega S) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
