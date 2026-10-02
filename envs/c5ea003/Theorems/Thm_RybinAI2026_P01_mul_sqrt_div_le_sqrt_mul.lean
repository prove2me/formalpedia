-- Prove2me | Theorems.Thm_RybinAI2026_P01_mul_sqrt_div_le_sqrt_mul
-- name    : RybinAI2026.P01.mul_sqrt_div_le_sqrt_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T03:27:03.218759+00:00
-- url     : https://prove2.me/theorems/a2171072-91f5-49c8-b103-29744b96c105
-- title:
--   Pointwise crux of the tail-bound reduction for the geometric-affinity target
-- statement:
--   For nonnegative reals f, g, positive A and nonnegative B with B f <= A g, one has f * sqrt(B/A) <= sqrt(f g).  This is the pointwise estimate used on the complement of the tail region {B f > A g}; after integrating it gives Int sqrt(f g) >= sqrt(B/A) * (A - T) and hence, with T <= A/2, the geometric-affinity target (1/2) sqrt(A B) <= Int sqrt(f g).
-- source:
--   P01 mission c36fd4df-ef29-4fbc-9bb6-1f6acf3c0733, root 8d67c9ac-a6c7-418c-b8db-0bc029c18484. Analytic heart of the reduction from one_sphere_affinity_tail_bound (44f4106d) to one_sphere_geometric_affinity (6698003b); derived in artifacts/p01_slack/2026-10-03-two-point-reformulation.md section 10.

import Mathlib

namespace RybinAI2026.P01

/-- Pointwise crux of the tail-bound reduction of the geometric-affinity target: on the region
where `B f <= A g`, the geometric mean `sqrt(f g)` dominates `f / sqrt(A/B)`. -/
theorem mul_sqrt_div_le_sqrt_mul {f g A B : ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g) (hA : 0 < A)
    (hB : 0 ≤ B) (h : B * f ≤ A * g) : f * Real.sqrt (B / A) ≤ Real.sqrt (f * g) := by sorry

end RybinAI2026.P01
