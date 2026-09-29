-- Prove2me | Theorems.Thm_bernoulli_centered_sampling_fluctuation_entry_sum_chernoff_mgf_bound
-- name    : bernoulli_centered_sampling_fluctuation_entry_sum_chernoff_mgf_bound
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-29T00:35:50.152425+00:00
-- url     : https://prove2.me/theorems/9cab4099-1d7a-40c5-ac1d-1c2931e407cf
-- statement:
--   One-sided Chernoff/MGF tail for the centered sampling fluctuation entry sum in the explicit finite-Bernoulli model. The statistic matrixEntrySum(centeredSamplingFluctuation Omega p X) = p^{-1} sum_w X_w (1[w in Omega] - p) is a centered sum of independent terms; its moment generating function factorizes over cells (via Finset.prod_add): E[exp(s Z)] = prod_w exp(-s p c_w)(1-p+p exp(s c_w)) with c_w = p^{-1} X_w, bounded by the Bennett form exp(sum_w p(exp(s c_w)-1-s c_w)). Markov then gives this one-sided Chernoff bound directly in the bernoulliEventProb model, with NO measure-theoretic bridge. Reusable core for the scalar-Bernstein proofs of Candes-Recht Lemma 6.6 (linear off-diagonal Neumann coefficient) and the quadratic Neumann coefficients: combine with the sub-gamma bound (bernstein_exp_le) and the min-dimension base bounds to obtain the pointwise two-term coefficient tails.

import Mathlib
import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem bernoulli_centered_sampling_fluctuation_entry_sum_chernoff_mgf_bound
    {n₁ n₂ : ℕ} (p s t : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs : 0 ≤ s) :
    bernoulliEventProb p (fun Ω => t < matrixEntrySum (centeredSamplingFluctuation Ω p X))
      ≤ Real.exp (-(s * t) + ∑ w : Fin n₁ × Fin n₂,
          p * (Real.exp (s * (p⁻¹ * X w.1 w.2)) - 1 - s * (p⁻¹ * X w.1 w.2))) := by sorry
