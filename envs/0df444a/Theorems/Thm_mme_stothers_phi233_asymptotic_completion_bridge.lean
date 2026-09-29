-- Prove2me | Theorems.Thm_mme_stothers_phi233_asymptotic_completion_bridge
-- name    : mme_stothers_phi233_asymptotic_completion_bridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:09:16.416347+00:00
-- url     : https://prove2.me/theorems/c082c967-a42d-449d-ae7d-68e1e9a02753
-- title:
--   End-to-end asymptotic completion bridge for phi_233
-- statement:
--   Every strictly positive stationary real $\varphi_{233}$ profile whose two marginals satisfy $2a+b<2/3$ and $a+c<1/2$ has exact integral approximants with subexponential same-marginal ambiguity. More precisely, there are integer profiles $(A_n,B_n,C_n,D_n)$ with $2A_n+B_n+C_n+D_n=n$, converging after normalization to $(a,b,c,d)$, and a finite shift $k>0$ such that for every $\varepsilon>0$, eventually
--
--   $$
--   |S_{n+k}|\le (2(n+k)+1)^{10}e^{2(n+k)\varepsilon}[6(2(n+k)+1)]^{10}|S_{0,n+k}|.
--   $$
--
--   Thus irrational stationary data can be used rigorously in the finite tensor-power extraction: exact rounding, positivity after a finite prefix, entropy continuity, and the target-versus-ambient count are all packaged in one theorem.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and the exceptional 233 constituent in Lemma 5.1, printed pp. 361 and 367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. This theorem formalizes the integral-rounding and subexponential-completion passage implicit in the asymptotic laser argument.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_stothers_phi233_exact_integer_profile_rounding
import Theorems.Thm_mme_stothers_phi233_rounded_tail_completion_ratio

open MME Filter

set_option autoImplicit false

theorem mme_stothers_phi233_asymptotic_completion_bridge
    (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotal : 2 * a + b + c + d = 1)
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0)
    (hsigmaUpper : 2 * a + b < 2 / 3)
    (hmuUpper : a + c < 1 / 2) :
    ∃ A B C D : ℕ → ℕ, ∃ k : ℕ,
      (∀ n, 2 * A n + B n + C n + D n = n) ∧
      Tendsto (fun n ↦ (A n : ℝ) / (n : ℝ)) atTop (nhds a) ∧
      Tendsto (fun n ↦ (B n : ℝ) / (n : ℝ)) atTop (nhds b) ∧
      Tendsto (fun n ↦ (C n : ℝ) / (n : ℝ)) atTop (nhds c) ∧
      Tendsto (fun n ↦ (D n : ℝ) / (n : ℝ)) atTop (nhds d) ∧
      0 < k ∧
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
