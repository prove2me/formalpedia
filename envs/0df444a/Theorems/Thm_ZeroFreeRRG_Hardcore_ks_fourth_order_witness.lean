-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_ks_fourth_order_witness
-- name    : ZeroFreeRRG.Hardcore.ks_fourth_order_witness
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T03:58:48.174644+00:00
-- url     : https://prove2.me/theorems/ee4e984a-9edb-46ca-b0b7-1ff138bbaa45
-- title:
--   Fourth-order cavity witnesses for the weak Kesten–Stigum bound
-- statement:
--   For the hardcore model with $0<\alpha<1/2$, and for the antiferromagnetic $q$-state Potts model with $0\le\beta<1$, there are positive constants $C$ and $\epsilon_0$ such that, for every $0<\epsilon<\epsilon_0$, some admissible cavity law $\nu$ satisfies $\mathcal B_{d,t}(\nu)\ge A\epsilon^4-C\epsilon^6$, where $A=\frac d4\kappa^2((d-1)\kappa^2-1)$. For hardcore $\kappa^2=(\alpha/(1-\alpha))^2$; for Potts $\kappa^2=((1-\beta)/(q-1+\beta))^2$. The constants may depend on $d$, $q$ and the parameter, and the Potts statement includes $\beta=0$. This is the lower-bound consequence of the source's fourth-order expansion for a symmetric two-point cavity law.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30, equation (26).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional

open scoped Classical

namespace ZeroFreeRRG.Hardcore
/-- Quantitative fourth-order cavity-law witnesses for the weak Kesten–Stigum bound:
Chen–Wang–Zhang (2026), proof of Lemma 4.17, equation (26). -/
theorem ks_fourth_order_witness (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q) :
    (∀ α : ℝ, 0 < α → α < 1 / 2 →
      ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ ν ∈ cavityLaws .hardcore α,
          ((d : ℝ) / 4) * (α / (1 - α))^2 *
            (((d : ℝ) - 1) * (α / (1 - α))^2 - 1) * ε^4 - C * ε^6 ≤
              betheK .hardcore α d ν) ∧
    (∀ β : ℝ, 0 ≤ β → β < 1 →
      ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ ν ∈ cavityLaws (.potts q) β,
          ((d : ℝ) / 4) * ((1-β) / ((q : ℝ)-1+β))^2 *
            (((d : ℝ) - 1) * ((1-β) / ((q : ℝ)-1+β))^2 - 1) * ε^4 - C * ε^6 ≤
              betheK (.potts q) β d ν) := by sorry
end ZeroFreeRRG.Hardcore
