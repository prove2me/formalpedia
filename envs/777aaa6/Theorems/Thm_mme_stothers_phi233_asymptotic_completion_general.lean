-- Prove2me | Theorems.Thm_mme_stothers_phi233_asymptotic_completion_general
-- name    : mme_stothers_phi233_asymptotic_completion_general
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T08:39:06.239983+00:00
-- url     : https://prove2.me/theorems/7b868b64-5de8-419f-a969-10e5cecdfd48
-- title:
--   Subexponential completion ambiguity for every positive stationary Stothers 233 profile
-- statement:
--   Let $a,b,c,d>0$ satisfy $2a+b+c+d=1$ and the stationary entropy equation
--   $$2(-\log(a/2)-1)-2(-\log(b/2)-1)-(-\log(c/2)-1)+(-\log(d/2)-1)=0.$$
--   There are exact integer profiles $(A_n,B_n,C_n,D_n)$ with $2A_n+B_n+C_n+D_n=n$, whose normalized coordinates converge to $(a,b,c,d)$, and an integer $k>0$ such that, for every $\varepsilon>0$ and all sufficiently large $n$,
--   $$M_{n+k}\le(2(n+k)+1)^{10}e^{2(n+k)\varepsilon}(6(2(n+k)+1))^{10}P_{n+k}.$$
--   Here $M_m$ counts all admissible addresses with the prescribed marginals of the integer profile, and $P_m$ counts its exact-profile addresses. No additional upper bounds on the two marginals are required.
-- source:
--   Generalization of the established Stothers 233 entropy and actual-degree isolation formalization.

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_stothers_phi233_cyclic_ambient_data
import Definitions.Def_mme_stothers_phi233_cyclic_finsets
open MME MME.StothersFourth MME.StothersFourth.Phi233 BigOperators Filter
set_option autoImplicit false

theorem mme_stothers_phi233_asymptotic_completion_general
    (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotal : 2 * a + b + c + d = 1)
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0)
    :
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
                  (C (n + k)) (D (n + k))) : ℝ) := by sorry
