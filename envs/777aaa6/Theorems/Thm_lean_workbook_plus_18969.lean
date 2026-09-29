-- Prove2me | Theorems.Thm_lean_workbook_plus_18969
-- name    : lean_workbook_plus_18969
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/1186b18b-71d2-4177-ae97-08b7c1b51df7
-- statement:
--   Use : $y^6+z^6-yz(y^4+z^4)=(y-z)(y^5-z^5) \ge 0 \rightarrow y^6+z^6 \ge yz(y^4+z^4)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18969 : ∀ y z : ℝ, y^6 + z^6 ≥ y * z * (y^4 + z^4)   :=  by sorry
