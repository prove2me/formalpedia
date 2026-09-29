-- Prove2me | Theorems.Thm_bernoulli_tangent_sampling_concentration_from_zero_rate_deviation_bound
-- name    : bernoulli_tangent_sampling_concentration_from_zero_rate_deviation_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T06:34:43.861972+00:00
-- url     : https://prove2.me/theorems/4144aae1-860b-4096-9d91-1c511a0d507c
-- statement:
--   This leaf isolates the zero-rate case in the Bernoulli tangent sampling transfer.
--
--   At $p=0$, the deterministic implication from normalized deviation to pointwise concentration is false for arbitrary fixed observation sets, because $0^{-1}=0$ in Lean. The Bernoulli probability statement is different: the Bernoulli model with $p=0$ assigns all probability mass to the empty observation set.
--
--   The theorem says that, at sampling rate $p=0$, any lower bound for the probability of the deviation event implies the same lower bound for the tangent concentration event:
--
--   $$
--   mathbb P_0{operatorname{TangentSamplingDeviationBound}(Omega,S,0,arepsilon)}ge 1-c n^{-eta}
--   quadLongrightarrowquad
--   mathbb P_0{operatorname{TangentSamplingConcentration}(Omega,S,0,arepsilon)}ge 1-c n^{-eta}.
--   $$
--
--   This node is the zero-rate companion to the positive-rate transfer theorem. Together they repair the deprecated proof of the original Bernoulli deviation-to-concentration node.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

theorem bernoulli_tangent_sampling_concentration_from_zero_rate_deviation_bound
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (epsilon c β : ℝ) :
    bernoulliEventProb (n1 := n₁) (n2 := n₂) 0
        (fun Omega => TangentSamplingDeviationBound Omega S 0 epsilon) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb (n1 := n₁) (n2 := n₂) 0
        (fun Omega => TangentSamplingConcentration Omega S 0 epsilon) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
