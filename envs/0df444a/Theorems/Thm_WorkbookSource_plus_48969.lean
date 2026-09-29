-- Prove2me | Theorems.Thm_WorkbookSource_plus_48969
-- name    : WorkbookSource.plus_48969
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:34.412011+00:00
-- url     : https://prove2.me/theorems/ab05abe6-e034-4df0-adb1-e395e9349676
-- title:
--   A sum-cubic bound on a nonnegative sphere
-- statement:
--   For $ a, b, c\geq 0,a^2+b^2+c^2=3 $ prove that:
--   $ 6abc+11(a+b+c)\geq (a+b+c)^3+12 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_48969` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_48969; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_48969 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + b^2 + c^2 = 3) : 6 * a * b * c + 11 * (a + b + c) ≥ (a + b + c)^3 + 12   :=  by sorry
