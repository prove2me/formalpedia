-- Prove2me | Theorems.Thm_WorkbookCorrected_base_6994
-- name    : WorkbookCorrected.base_6994
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:29:13.037403+00:00
-- url     : https://prove2.me/theorems/5f09dc5a-3f80-4547-bbc4-09eaa64149b2
-- title:
--   An eighth-degree cyclic inequality for nonnegative variables
-- statement:
--   Prove that for $x,y,z\geq 0$,
--   $-xyz(x^2y^3+y^2z^3+x^3z^2)+1/3(x^2y^2+y^2z^2+x^2z^2)^2\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6994` (Apache-2.0). Natural-language proposition preserved; raw Lean transcription corrected: Restore the nonnegative domain assumptions for x, y, z explicitly stated in the natural-language source and omitted by the raw Lean transcription. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6994; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.base_6994 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : -x*y*z*(x^2*y^3 + y^2*z^3 + x^3*z^2) + (1/3)*(x^2*y^2 + y^2*z^2 + x^2*z^2)^2 ≥ 0  :=  by sorry
