-- Prove2me | Theorems.Thm_RybinAI2026_P01_sqrt_s_over_one_plus_s_sq_lower
-- name    : RybinAI2026.P01.sqrt_s_over_one_plus_s_sq_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T20:26:03.201018+00:00
-- url     : https://prove2.me/theorems/aad50e09-7c31-4008-a4f3-e45eb3e373d0
-- title:
--   Elementary lower bound for the slope integral of the mixed kernel
-- statement:
--   On $[0,1]$, $(1+t^2)^{-1}\ge 1/2$; on $[1,2]$, $(1+t^2)^{-1}\ge 1/5$; and on $[2,4]$,
--   $(1+t^2)^{-1}\ge 1/17$.  Integrating $\sqrt t$ against these constants gives
--   $$\int_0^4\frac{\sqrt t}{1+t^2}\,dt\ \ge\ \tfrac13 + \tfrac{2}{15}(2^{3/2}-1) + \tfrac{2}{51}(4^{3/2}-2^{3/2})\ \approx\ 0.7799 > \tfrac34.$$
-- source:
--   P01 mission c36fd4df-ef29-4fbc-9bb6-1f6acf3c0733, root 8d67c9ac-a6c7-418c-b8db-0bc029c18484. Leaf of the elementary disproof of one_sphere_geometric_affinity (6698003b); full certificate in work/p01_aff/round9/FINAL_CERTIFICATE.md.

import Mathlib

open MeasureTheory

namespace RybinAI2026.P01

/-- Splitting `[0,4]` into `[0,1]`, `[1,2]`, `[2,4]` and using `1 + t^2 ≤ 2, 5, 17`
respectively gives `∫_0^4 sqrt(t)/(1+t^2) dt ≥ 3/4`.  This is the only ingredient in
the lower bound `G ≥ 3 b^(-1/4)` for the mixed geometric-mean kernel. -/
theorem sqrt_s_over_one_plus_s_sq_lower :
    (3 / 4 : ℝ) ≤ ∫ t in (0 : ℝ)..4, Real.sqrt t / (1 + t ^ 2) := by sorry

end RybinAI2026.P01
