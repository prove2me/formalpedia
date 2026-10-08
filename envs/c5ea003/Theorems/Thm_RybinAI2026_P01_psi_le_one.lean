-- Prove2me | Theorems.Thm_RybinAI2026_P01_psi_le_one
-- name    : RybinAI2026.P01.psi_le_one
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-02T20:26:00.413125+00:00
-- url     : https://prove2.me/theorems/05757aab-6d0c-445e-9179-cb46b4916870
-- title:
--   The reciprocal-diagonal psi integral is at most one on the unit parameter range
-- statement:
--   For $0<t\le 1$ and $s\in[0,1]$ we have $1+(t-1)s^2 \le 1$, so the integrand is at most $1$ and
--   $\int_0^1 (1+(t-1)s^2)^{-1}\,ds \le 1$.  This bounds $F_1 = 4\,\psi(t)$ by $4$.
-- source:
--   P01 mission c36fd4df-ef29-4fbc-9bb6-1f6acf3c0733, root 8d67c9ac-a6c7-418c-b8db-0bc029c18484. Leaf of the elementary disproof of one_sphere_geometric_affinity (6698003b); full certificate in work/p01_aff/round9/FINAL_CERTIFICATE.md.

import Mathlib

open MeasureTheory

namespace RybinAI2026.P01

/-- For `0 < t <= 1` the integrand `1/(1 + (t-1) s^2)` is at most `1` on `[0,1]`, because
`1 + (t-1) s^2 <= 1`.  Hence `psi t <= 1`, i.e. `F1 = 4 psi t <= 4`. -/
theorem psi_le_one {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹) ≤ 1 := by sorry

end RybinAI2026.P01
