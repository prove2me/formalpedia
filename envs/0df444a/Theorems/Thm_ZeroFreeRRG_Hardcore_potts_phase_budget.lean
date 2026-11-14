-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_phase_budget
-- name    : ZeroFreeRRG.Hardcore.potts_phase_budget
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:55:38.1662+00:00
-- url     : https://prove2.me/theorems/4412b306-5049-4b7c-808b-11a43f3e2abb
-- title:
--   Numerical phase budget for the Potts zero-free disk
-- statement:
--   For $d\ge3$ and $0\le\delta<0.35/d$, the quantity $$\frac{d\delta}{(7/8)(1-\delta)}$$ is strictly less than $1/2$. This is the numerical margin for the phase-distance induction in the Potts zero-free disk.
-- source:
--   Auxiliary numerical bound for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
set_option autoImplicit false

theorem ZeroFreeRRG.Hardcore.potts_phase_budget (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : δ < (0.35:ℝ)/(d:ℝ)) :
    δ*(d:ℝ) / (((7:ℝ)/8)*(1-δ)) < 1/2 := by sorry
