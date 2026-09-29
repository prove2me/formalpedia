-- Prove2me | Theorems.Thm_mme_stothers_phi233_rounded_tail_completion_ratio
-- name    : mme_stothers_phi233_rounded_tail_completion_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:04:41.088966+00:00
-- url     : https://prove2.me/theorems/952123c7-2a3b-4739-96c1-af96158e5f1a
-- title:
--   Automatic subexponential completion bound after a finite rounding prefix
-- statement:
--   Let integral profiles $(A_n,B_n,C_n,D_n)$ satisfy $2A_n+B_n+C_n+D_n=n$ and converge after normalization to a strictly positive stationary $\varphi_{233}$ profile $(a,b,c,d)$. Assume the limiting marginals obey $2a+b<2/3$ and $a+c<1/2$. Then there is a finite shift $k>0$ such that, for every $\varepsilon>0$, eventually
--
--   $$
--   |S_{n+k}|\le (2(n+k)+1)^{10}e^{2(n+k)\varepsilon}[6(2(n+k)+1)]^{10}|S_{0,n+k}|.
--   $$
--
--   Here $S_0$ is the exact-profile address family and $S$ the full same-marginal family. In particular, positivity and the stationary completion profile required by the entropy argument need not be supplied at every rounded scale: convergence guarantees them automatically after a finite prefix. This is the ready-to-use asymptotic completion estimate for rounded irrational stationary data.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and the exceptional 233 constituent in Lemma 5.1, printed pp. 361 and 367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. This theorem packages the finite-prefix argument implicit in passing from real entropy optimizers to integral tensor-power profiles.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_stothers_phi233_rounded_completion_ratio_subexponential
import Theorems.Thm_mme_stothers_phi233_stationary_profile_sequence_exists

open MME Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem mme_stothers_phi233_rounded_tail_completion_ratio
    (A B C D : ℕ → ℕ) (a b c d : ℝ)
    (hsum : ∀ n, 2 * A n + B n + C n + D n = n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotal : 2 * a + b + c + d = 1)
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0)
    (hsigmaUpper : 2 * a + b < 2 / 3)
    (hmuUpper : a + c < 1 / 2)
    (hA : Tendsto (fun n ↦ (A n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hB : Tendsto (fun n ↦ (B n : ℝ) / (n : ℝ)) atTop (nhds b))
    (hC : Tendsto (fun n ↦ (C n : ℝ) / (n : ℝ)) atTop (nhds c))
    (hD : Tendsto (fun n ↦ (D n : ℝ) / (n : ℝ)) atTop (nhds d)) :
    ∃ k : ℕ, 0 < k ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          (Nat.card
              (MME.StothersFourth.Phi233.MarginalAddress
                (n + k) (A (n + k)) (B (n + k))
                (C (n + k)) (D (n + k))) : ℝ) ≤
            (((2 * (n + k) + 1 : ℕ) : ℝ)) ^ 10 *
              Real.exp (((2 * (n + k) : ℕ) : ℝ) * ε) *
              (6 * (((2 * (n + k) + 1 : ℕ) : ℝ))) ^ 10 *
              (Nat.card
                (MME.StothersFourth.Phi233.ExactProfileAddress
                  (n + k) (A (n + k)) (B (n + k))
                  (C (n + k)) (D (n + k))) : ℝ) := by
  sorry
