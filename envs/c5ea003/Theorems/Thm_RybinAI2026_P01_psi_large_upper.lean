-- Prove2me | Theorems.Thm_RybinAI2026_P01_psi_large_upper
-- name    : RybinAI2026.P01.psi_large_upper
-- status  : Open
-- author  : @WillR
-- created : 2026-10-02T20:26:29.210995+00:00
-- url     : https://prove2.me/theorems/e1914e98-4279-4ad5-8ea8-c2ed1c99a7e5
-- title:
--   Upper bound for the reciprocal-diagonal psi integral at a large parameter
-- statement:
--   Let $c = 1/b-1>0$.  Substituting $s=u/\sqrt c$ gives
--   $$\int_0^1\frac{ds}{1+cs^2}=\frac{1}{\sqrt c}\int_0^{\sqrt c}\frac{du}{1+u^2}.$$
--   Splitting the last integral at $u=1$ and using $(1+u^2)^{-1}\le 1$ on $[0,1]$ and
--   $(1+u^2)^{-1}\le u^{-2}$ on $[1,\infty)$ bounds it by $1+1=2$.  Hence
--   $\psi(1/b) \le 2/\sqrt{1/b-1}$.
-- source:
--   P01 mission c36fd4df-ef29-4fbc-9bb6-1f6acf3c0733, root 8d67c9ac-a6c7-418c-b8db-0bc029c18484. Leaf of the elementary disproof of one_sphere_geometric_affinity (6698003b); full certificate in work/p01_aff/round9/FINAL_CERTIFICATE.md.

import Mathlib

open MeasureTheory

namespace RybinAI2026.P01

/-- Rescaling `s = u / sqrt c` with `c = 1/b - 1 > 0` gives
`psi (1/b) = (1/sqrt c) ∫_0^sqrt c (1+u^2)⁻¹ du`, and `∫_0^T (1+u^2)⁻¹ du ≤ 2`
for every `T ≥ 0` because `(1+u^2)⁻¹ ≤ 1` on `[0,1]` and `(1+u^2)⁻¹ ≤ u⁻²` on `[1,∞)`.
This bounds `F2 = 4 psi(1/b)/b` and is the only place a `pi` constant enters
(through `atan T ≤ π/2 < 2`). -/
theorem psi_large_upper {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    (∫ s in (0 : ℝ)..1, (1 + ((1 / b) - 1) * s ^ 2)⁻¹) ≤ 2 / Real.sqrt ((1 / b) - 1) := by sorry

end RybinAI2026.P01
