-- Prove2me | Theorems.Thm_bernoulli_centered_sampling_fluctuation_two_term_bernstein_tail
-- name    : bernoulli_centered_sampling_fluctuation_two_term_bernstein_tail
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-30T00:20:49.875627+00:00
-- url     : https://prove2.me/theorems/270d8ab7-f3c0-4ffa-8465-f7529262752e
-- statement:
--   Two-term (Bernstein) concentration tail for the centered sampling fluctuation entry sum, proved directly in the explicit finite-Bernoulli model (no measure-theoretic bridge). For Z = matrixEntrySum(centeredSamplingFluctuation Omega p X) = sum_w (X_w/p)(1[w in Omega]-p), with variance proxy v = frobeniusNormSq X / p and range R = entrySupNorm X / p, the standard two-term Bernstein bound holds: P(|Z| > sqrt(2 v u) + (2/3) R u) <= 2 exp(-u). Proof chain (all in bernoulliEventProb): MGF factorization via Finset.prod_add, Bennett MGF bound, Markov/Chernoff, sub-gamma per-term bound (using bernstein_exp_le and e^y-1-y<=y^2/2 for y<=0), optimization s=u-scaled, and the two-term threshold lemma. This is the reusable scalar-Bernstein core for Candes-Recht Lemma 6.6 (off-diagonal linear Neumann coefficient): with u=(beta+2)log n and the min-dimension base bounds on frobeniusNorm/entrySupNorm of the coefficient base matrix, it yields the pointwise coefficient tails, then (union over coordinates) the uniform coefficient bound.

import Mathlib
import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem bernoulli_centered_sampling_fluctuation_two_term_bernstein_tail
    {n₁ n₂ : ℕ} (p u : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hu : 0 ≤ u) (hfro : 0 < frobeniusNormSq X) :
    bernoulliEventProb p (fun Ω =>
        Real.sqrt (2 * (frobeniusNormSq X / p) * u) + (2 / 3) * (entrySupNorm X / p) * u
          < |matrixEntrySum (centeredSamplingFluctuation Ω p X)|)
      ≤ 2 * Real.exp (-u) := by sorry
