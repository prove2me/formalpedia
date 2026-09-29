-- Prove2me | Theorems.Thm_mme_CW_q6_coupled_rounding_package
-- name    : mme_CW_q6_coupled_rounding_package
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T05:02:50.922278+00:00
-- url     : https://prove2.me/theorems/6d8555d3-a1ce-4b24-a27c-29ad911d6c03
-- title:
--   Floor-rounded type counts for the q=6 coupled CW constituent
-- statement:
--   Fix a real parameter $\tau$ with $3\tau \ge 2$, and put $Q=6^{3\tau}$. There are integer type counts $L_N,G_N$ at every scale $N$ such that
--
--   $$
--   L_N+G_N=N, \qquad \frac{L_N}{N}\longrightarrow \frac{2}{Q+2}, \qquad \frac{G_N}{N}\longrightarrow \frac{Q}{Q+2}.
--   $$
--
--   Moreover, for all sufficiently large $N$, $L_N>0$ and
--
--   $$
--   341L_N<100G_N.
--   $$
--
--   Thus the finite integer counts eventually satisfy the strict pruning condition $G_N/L_N>3.41$ used in the coupled Salem--Spencer extraction, while converging to the real proportions that optimize the auxiliary estimate. The cross-multiplied formulation avoids division by zero and does not use truncated natural-number division.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), proof of the coupled-value lemma, journal pp. 270--272 (PDF pp. 20--22), especially L=floor(2N/(q^(3 tau)+2)), G=N-L and the condition G/L>3.41; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Filter

theorem mme_CW_q6_coupled_rounding_package
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ L G : ℕ → ℕ,
      (∀ N, L N + G N = N) ∧
      Tendsto (fun N : ℕ => (L N : ℝ) / (N : ℝ)) atTop
        (nhds (2 / ((6 : ℝ) ^ (3 * tau) + 2))) ∧
      Tendsto (fun N : ℕ => (G N : ℝ) / (N : ℝ)) atTop
        (nhds ((6 : ℝ) ^ (3 * tau) /
          ((6 : ℝ) ^ (3 * tau) + 2))) ∧
      ∀ᶠ N : ℕ in atTop,
        0 < L N ∧ 341 * L N < 100 * G N := by sorry
