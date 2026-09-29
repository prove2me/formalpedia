-- Prove2me | Theorems.Thm_lean_workbook_plus_50690
-- name    : lean_workbook_plus_50690
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/af6e55e6-1140-48d6-9e1b-371abb522f2f
-- statement:
--   Prove that for $x, y, z \in \mathbb{R}$ and $u, v, w > 0$, the following inequality holds:\n$x^2wv(v+w) + y^2uw(w+u) + z^2vu(v+u) \geq 2(xy + zx + yz)uvw$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50690 (x y z u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) : x^2 * w * v * (v + w) + y^2 * u * w * (w + u) + z^2 * v * u * (v + u) ≥ 2 * (x * y + z * x + y * z) * u * v * w   :=  by sorry
