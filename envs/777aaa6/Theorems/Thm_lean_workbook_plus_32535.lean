-- Prove2me | Theorems.Thm_lean_workbook_plus_32535
-- name    : lean_workbook_plus_32535
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c2282288-1f99-467b-b4ab-1efbac464994
-- statement:
--   Given positive real numbers $u, v, w$ , we have: $(u+v)(v+w)(w+u) \geq 8uvw$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32535 (u v w : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) : (u + v) * (v + w) * (w + u) ≥ 8 * u * v * w   :=  by sorry
