-- Prove2me | Theorems.Thm_mme_stothers_phi134_four_count_rounding
-- name    : mme_stothers_phi134_four_count_rounding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:44:56.267929+00:00
-- url     : https://prove2.me/theorems/9e4b485e-c106-41ec-b583-32e77fc44753
-- title:
--   Boundary-safe integer rounding for the phi_134 profile
-- statement:
--   Let $a,c,\sigma$ satisfy $a>0$, $c>0$, $c\leq\sigma$, and $\sigma+a\leq1$. There are natural-number sequences $A_n,B_n,C_n,D_n$ such that
--
--   $$A_n+B_n+C_n+D_n=n$$
--
--   for every $n$, and
--
--   $$\frac{A_n}{n}\to a,\qquad \frac{B_n}{n}\to\sigma-c,\qquad \frac{C_n}{n}\to c,\qquad \frac{D_n}{n}\to1-\sigma-a.$$
--
--   The construction is valid on the boundary when either omitted profile weight is zero. These are precisely the integral multiplicities $(\alpha,\beta,\gamma,\delta)$ needed for the symmetric eight-type profile in Davie–Stothers Lemma 5.1(iii).
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 5.1(iii), printed p. 365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.SpecificLimits.Basic

open Filter

set_option autoImplicit false

theorem mme_stothers_phi134_four_count_rounding
    (sigma a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1) :
    ∃ A B C D : ℕ → ℕ,
      (∀ n, A n + B n + C n + D n = n) ∧
      Tendsto (fun n : ℕ ↦ (A n : ℝ) / (n : ℝ)) atTop (nhds a) ∧
      Tendsto (fun n : ℕ ↦ (B n : ℝ) / (n : ℝ)) atTop
        (nhds (sigma - c)) ∧
      Tendsto (fun n : ℕ ↦ (C n : ℝ) / (n : ℝ)) atTop (nhds c) ∧
      Tendsto (fun n : ℕ ↦ (D n : ℝ) / (n : ℝ)) atTop
        (nhds (1 - sigma - a)) := by
  sorry
