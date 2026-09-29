-- Prove2me | Theorems.Thm_mme_stothers_phi134_analytic_profile_surplus
-- name    : mme_stothers_phi134_analytic_profile_surplus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:08:42.446573+00:00
-- url     : https://prove2.me/theorems/eeef7a43-f9ea-4f27-a8fc-9d69e9123f7b
-- title:
--   Analytic surplus from convergent phi_134 profile sequences
-- statement:
--   Let $(A_n,B_n,C_n,D_n)$ be integral symmetric-profile multiplicities for $\phi_{134}$, summing to $n$, whose normalized limits are
--
--   $$a,\qquad \sigma-c,\qquad c,\qquad 1-\sigma-a.$$
--
--   Let $d_n$ be a positive collision-degree bound and $T_n$ the exact-profile cardinality. Assume their finite capacity satisfies the three-marginal entropy lower bound with polynomial loss $(6(2n+1))^{15}$. For every positive $V$ strictly below
--
--   $$8\left(\frac L\sigma\right)^\sigma\left(\frac E{1-\sigma}\right)^{1-\sigma}\left(\frac1a\right)^a\left(\frac{H/2}{c}\right)^c\left(\frac E{1-a-c}\right)^{1-a-c},$$
--
--   there is some positive $n$ for which
--
--   $$V^{2n}d_n\exp\!\bigl(4000\sqrt{12n+1}\bigr)<T_n^3L^{2B_n+2C_n}E^{2A_n+2B_n+4D_n}H^{2C_n}.$$
--
--   This is the boundary-safe analytic surplus step in Davie–Stothers Lemma 5.1(iii). It is deliberately parameterized by the finite counting layer, so the exact-profile cardinality and collision-degree formalizations can instantiate it without duplicating the limiting argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 5.1(iii), printed p. 365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib
import Theorems.Thm_mme_stothers_phi134_entropy_rate_identity

open MME Real BigOperators Filter

set_option autoImplicit false

theorem mme_stothers_phi134_analytic_profile_surplus
    (sigma a c L E H V : ℝ)
    (A B C D degree targetCard : ℕ → ℕ)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (hL : 0 < L) (hE : 0 < E) (hH : 0 < H)
    (hV : 0 < V)
    (hVlt :
      V <
        8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c)))
    (hsum : ∀ n, A n + B n + C n + D n = n)
    (hA : Tendsto (fun n : ℕ ↦ (A n : ℝ) / n) atTop (nhds a))
    (hB : Tendsto (fun n : ℕ ↦ (B n : ℝ) / n) atTop
      (nhds (sigma - c)))
    (hC : Tendsto (fun n : ℕ ↦ (C n : ℝ) / n) atTop (nhds c))
    (hD : Tendsto (fun n : ℕ ↦ (D n : ℝ) / n) atTop
      (nhds (1 - sigma - a)))
    (hdegree : ∀ n, 0 < n → 0 < degree n)
    (hcapacity : ∀ n : ℕ, 0 < n →
      Real.exp ((2 * n : ℝ) *
        (let an := (A n : ℝ) / n
         let cn := (C n : ℝ) / n
         let sn := ((B n : ℝ) + C n) / n
         (3 - cn) * Real.log 2 +
           Real.negMulLog sn + Real.negMulLog (1 - sn) +
           Real.negMulLog an + Real.negMulLog cn +
           Real.negMulLog (1 - an - cn))) ≤
        (6 * ((2 * n + 1 : ℕ) : ℝ)) ^ (15 : ℕ) *
          ((targetCard n : ℝ) ^ (3 : ℕ) / (degree n : ℝ))) :
    ∃ n : ℕ, 0 < n ∧ A n + B n + C n + D n = n ∧
      V ^ (2 * n) * (degree n : ℝ) *
          Real.exp (4000 * Real.sqrt ((12 * n + 1 : ℕ) : ℝ)) <
        (targetCard n : ℝ) ^ (3 : ℕ) *
          (L ^ (2 * B n + 2 * C n) *
            E ^ (2 * A n + 2 * B n + 4 * D n) *
            H ^ (2 * C n)) := by
  sorry
