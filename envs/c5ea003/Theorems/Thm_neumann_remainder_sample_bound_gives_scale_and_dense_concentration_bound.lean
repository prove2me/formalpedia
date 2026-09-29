-- Prove2me | Theorems.Thm_neumann_remainder_sample_bound_gives_scale_and_dense_concentration_bound
-- name    : neumann_remainder_sample_bound_gives_scale_and_dense_concentration_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T04:37:42.543161+00:00
-- url     : https://prove2.me/theorems/9b6fd397-0367-4634-8f0c-6415bb759de2
-- statement:
--   Source: Candes-Recht 2008, PDF pp. 18-21: Theorem 4.1/Theorem 4.2 for tangent-space concentration and Lemma 4.8 for the Neumann certificate tail.
--
--   This is the scalar constant-absorption bridge needed by the repaired Lemma 4.8 branch.  For a fixed tangent-deviation constant $C_{\mathrm{dev}}$, choose the remainder sample constant $C_R$ large enough so that the lower bound
--   $$
--   m\ge C_R\,\mu_0\,n\,r\,\beta\log n
--   $$
--   implies both estimates required by the proof:
--   $$
--   \operatorname{tangentSamplingDeviationScale}(C_{\mathrm{dev}},\beta,\mu_0,n,r,m)\le \frac12
--   $$
--   and the dense concentration lower bound
--   $$
--   m\ge \beta\mu_0nr\log n.
--   $$
--   The first conclusion is the arithmetic scale condition in Lemma 4.8; the second conclusion lets the repaired parent call the corrected dense tangent-concentration theorem instead of the deprecated no-density theorem.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem neumann_remainder_sample_bound_gives_scale_and_dense_concentration_bound
    (Cdev : ℝ) :
    ∃ CR : ℝ, 0 < CR ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n r m : ℕ) (μ₀ : ℝ),
        0 < n → 0 < r → 1 ≤ μ₀ →
        (m : ℝ) ≥ CR * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ)) →
        tangentSamplingDeviationScale Cdev β μ₀ n r m ≤ (1 : ℝ) / 2 ∧
          (m : ℝ) ≥ β * μ₀ * (n : ℝ) * (r : ℝ) *
            Real.log (n : ℝ) := by
  sorry
