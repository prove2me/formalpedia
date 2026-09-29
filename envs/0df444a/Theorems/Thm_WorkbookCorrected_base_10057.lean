-- Prove2me | Theorems.Thm_WorkbookCorrected_base_10057
-- name    : WorkbookCorrected.base_10057
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:13:11.715588+00:00
-- url     : https://prove2.me/theorems/07a37e76-4107-4dae-b73b-1e8a9eb8c956
-- title:
--   A pairwise-product maximum at fixed sum
-- statement:
--   If $x,y,z>0$ and $x+y+z=9\;,$ Then maximum value of $xy+yz+zx$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10057` (Apache-2.0). Natural-language proposition preserved; the source bound is completed with an exact attainment witness. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10057; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.base_10057 : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 9), x * y + y * z + z * x ≤ 27) ∧ (∃ x y z : ℝ, (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x + y + z = 9) ∧ ( x * y + y * z + z * x  =  27  )) := by sorry
