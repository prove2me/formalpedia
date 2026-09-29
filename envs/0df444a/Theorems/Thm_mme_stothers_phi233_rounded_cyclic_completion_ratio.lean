-- Prove2me | Theorems.Thm_mme_stothers_phi233_rounded_cyclic_completion_ratio
-- name    : mme_stothers_phi233_rounded_cyclic_completion_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:21:52.653881+00:00
-- url     : https://prove2.me/theorems/ef7d1131-0407-4be0-b04e-9195d1cf49a3
-- title:
--   Subexponential cyclic completion ratio along rounded phi_233 profiles
-- statement:
--   Let $(A_n,B_n,C_n,D_n)$ be exact integral profiles converging to a strictly positive stationary $\varphi_{233}$ profile in the interior marginal region. After discarding a finite prefix, for every $\varepsilon>0$ the associated cyclic ambient and target families obey
--
--   $$
--   |A_{\mathrm{cyc},n}| \le \Big((2n+1)^{10}e^{2n\varepsilon}[6(2n+1)]^{10}\Big)^3 |T_{\mathrm{cyc},n}|.
--   $$
--
--   The theorem states the completion estimate directly in the finite three-mode edge families used by the type-2 hashing argument. The loss is subexponential in the tensor-power parameter; cyclic symmetrization cubes the one-coordinate loss but introduces no further exponential term.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and the exceptional phi_233 estimate in Lemma 5.1(v), pp. 356--361 and 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_finsets
import Theorems.Thm_mme_stothers_phi233_rounded_tail_completion_ratio
import Theorems.Thm_mme_stothers_phi233_cyclic_cardinality_ratio

open MME Filter

set_option autoImplicit false

theorem mme_stothers_phi233_rounded_cyclic_completion_ratio
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
          ((MME.StothersFourth.Phi233.ambientFinset
              (n + k) (A (n + k)) (B (n + k))
              (C (n + k)) (D (n + k))).card : ℝ) ≤
            ((((2 * (n + k) + 1 : ℕ) : ℝ)) ^ 10 *
                Real.exp (((2 * (n + k) : ℕ) : ℝ) * ε) *
                (6 * (((2 * (n + k) + 1 : ℕ) : ℝ))) ^ 10) ^ 3 *
              ((MME.StothersFourth.Phi233.targetFinset
                (n + k) (A (n + k)) (B (n + k))
                (C (n + k)) (D (n + k))).card : ℝ) := by
  sorry
