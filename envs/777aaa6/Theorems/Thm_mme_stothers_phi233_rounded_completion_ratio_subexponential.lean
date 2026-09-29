-- Prove2me | Theorems.Thm_mme_stothers_phi233_rounded_completion_ratio_subexponential
-- name    : mme_stothers_phi233_rounded_completion_ratio_subexponential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:58:34.033645+00:00
-- url     : https://prove2.me/theorems/04b9116c-bc82-450d-b7e4-b7ecc8f9d96d
-- title:
--   Subexponential same-marginal completion ratio along rounded phi_233 profiles
-- statement:
--   Let integral target profiles $(A_n,B_n,C_n,D_n)$ of total length $N_n$ converge after normalization to a strictly positive stationary $\varphi_{233}$ profile $(a,b,c,d)$. At every scale, suppose $(X_n,Y_n,Z_n,W_n)$ is a strictly positive stationary profile with exactly the target profile's two independent marginals, with those marginals in the interior range required by the counting theorem. Then, for every $\varepsilon>0$, eventually
--
--   $$
--   |S_n|\le (2N_n+1)^{10}e^{2N_n\varepsilon}[6(2N_n+1)]^{10}|S_{0,n}|,
--   $$
--
--   where $S_{0,n}$ is the exact-profile address family and $S_n$ is the full same-marginal completion family. Thus the completion ambiguity is subexponential along rounded profiles: its only non-polynomial loss is $e^{2N_n\varepsilon}$ for arbitrary $\varepsilon>0$. This is the analytic target-versus-ambient estimate required by the exceptional $\varphi_{233}$ laser extraction when the ideal stationary marginals are irrational.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and the exceptional 233 constituent in Lemma 5.1, printed pp. 361 and 367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. The explicit polynomial factors come from the already formalized multinomial entropy bounds.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_stothers_phi233_exact_profile_entropy_polynomial_lower
import Theorems.Thm_mme_stothers_phi233_log_stationarity_of_critical_product
import Theorems.Thm_mme_stothers_phi233_stationary_marginal_address_entropy_upper
import Theorems.Thm_mme_stothers_phi233_uniform_entropy_stability

open MME Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem mme_stothers_phi233_rounded_completion_ratio_subexponential
    (N A B C D : ℕ → ℕ) (X Y Z W : ℕ → ℝ)
    (a b c d : ℝ)
    (hN : ∀ n, 0 < N n)
    (hsum : ∀ n, 2 * A n + B n + C n + D n = N n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotal : 2 * a + b + c + d = 1)
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0)
    (hA : Tendsto (fun n ↦ (A n : ℝ) / (N n : ℝ)) atTop (nhds a))
    (hB : Tendsto (fun n ↦ (B n : ℝ) / (N n : ℝ)) atTop (nhds b))
    (hC : Tendsto (fun n ↦ (C n : ℝ) / (N n : ℝ)) atTop (nhds c))
    (hD : Tendsto (fun n ↦ (D n : ℝ) / (N n : ℝ)) atTop (nhds d))
    (hX : ∀ n, 0 < X n) (hY : ∀ n, 0 < Y n)
    (hZ : ∀ n, 0 < Z n) (hW : ∀ n, 0 < W n)
    (htotalX : ∀ n, 2 * X n + Y n + Z n + W n = 1)
    (hsigmaX : ∀ n,
      2 * X n + Y n =
        2 * ((A n : ℝ) / (N n : ℝ)) + (B n : ℝ) / (N n : ℝ))
    (hmuX : ∀ n,
      X n + Z n = (A n : ℝ) / (N n : ℝ) + (C n : ℝ) / (N n : ℝ))
    (hsigmaUpper : ∀ n,
      2 * ((A n : ℝ) / (N n : ℝ)) + (B n : ℝ) / (N n : ℝ) < 2 / 3)
    (hmuUpper : ∀ n,
      (A n : ℝ) / (N n : ℝ) + (C n : ℝ) / (N n : ℝ) < 1 / 2)
    (hcritical : ∀ n,
      (X n) ^ (2 : ℕ) * W n = (Y n) ^ (2 : ℕ) * Z n) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (Nat.card
            (MME.StothersFourth.Phi233.MarginalAddress
              (N n) (A n) (B n) (C n) (D n)) : ℝ) ≤
          (((2 * N n + 1 : ℕ) : ℝ)) ^ 10 *
            Real.exp (((2 * N n : ℕ) : ℝ) * ε) *
            (6 * (((2 * N n + 1 : ℕ) : ℝ))) ^ 10 *
            (Nat.card
              (MME.StothersFourth.Phi233.ExactProfileAddress
                (N n) (A n) (B n) (C n) (D n)) : ℝ) := by
  sorry
