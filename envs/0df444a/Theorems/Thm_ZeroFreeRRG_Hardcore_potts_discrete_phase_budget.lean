-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_discrete_phase_budget
-- name    : ZeroFreeRRG.Hardcore.potts_discrete_phase_budget
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:09:45.307758+00:00
-- url     : https://prove2.me/theorems/0ec3984d-2297-4b32-856d-9e1986fc007d
-- title:
--   Numerical budget for discrete Potts phase changes
-- statement:
--   For $d\ge3$ and $0\le\delta<0.35/d$, put $r=\delta/((7/8)(1-\delta))$. Then $r\le96/625$ and $d(25/23)r<1/2$.
-- source:
--   Auxiliary step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_discrete_phase_budget (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : δ < (0.35:ℝ)/(d:ℝ)) :
    let r := δ / (((7:ℝ)/8)*(1-δ))
    0 ≤ r ∧ r ≤ 96/625 ∧ (d:ℝ)*(25/23)*r < 1/2 := by sorry
