-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_fourth_order_witness
-- name    : ZeroFreeRRG.Hardcore.hardcore_fourth_order_witness
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:29:36.977207+00:00
-- url     : https://prove2.me/theorems/c70ad973-a0a9-4863-ac52-8cd006eb15d7
-- title:
--   Hardcore fourth-order Bethe witness
-- statement:
--   Fix an integer $d\ge3$ and $\alpha\in(0,1/2)$, and write $\theta=\alpha/(1-\alpha)$. There exist constants $C,\varepsilon_0>0$ such that, for every $\varepsilon\in(0,\varepsilon_0)$, some admissible hardcore cavity law $\nu$ satisfies
--
--   $$\mathcal B_{d,\alpha}(\nu)\ge \frac d4\theta^2\bigl((d-1)\theta^2-1\bigr)\varepsilon^4-C\varepsilon^6.$$
--
--   This quantitative witness is the hardcore part of the fourth-order perturbation argument yielding the weak Kesten–Stigum inequality from the variational bound. Here $\mathcal B_{d,\alpha}(\nu)$ denotes the paper's Bethe functional evaluated at $\nu$.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://arxiv.org/abs/2610.40510, proof of Lemma 4.17, equation (26), pp. 30–31; quantitative hardcore witness.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical

namespace ZeroFreeRRG.Hardcore
 theorem hardcore_fourth_order_witness (d : ℕ) (hd : 3 ≤ d) (α : ℝ)
    (hα : 0 < α) (hα2 : α < 1/2) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ ν ∈ cavityLaws .hardcore α,
        ((d : ℝ) / 4) * (α / (1 - α))^2 *
          (((d : ℝ) - 1) * (α / (1 - α))^2 - 1) * ε^4 - C * ε^6 ≤
            betheK .hardcore α d ν := by sorry
end ZeroFreeRRG.Hardcore
