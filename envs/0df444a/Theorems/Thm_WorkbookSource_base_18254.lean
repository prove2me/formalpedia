-- Prove2me | Theorems.Thm_WorkbookSource_base_18254
-- name    : WorkbookSource.base_18254
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:32:32.864795+00:00
-- url     : https://prove2.me/theorems/41406dfb-20bc-41bd-90fe-a5bdc9bfbbbd
-- title:
--   A refined squared reciprocal sum inequality
-- statement:
--   Let a,b,c>0.Prove: $\frac{1}{a^2}+\frac{1}{b^2}+\frac{1}{c^2}+\frac{1}{(a+b+c)^2}\geq \frac{7}{25}(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}+\frac{1}{a+b+c})^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18254` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18254; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18254 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 + 1 / (a + b + c) ^ 2) ≥ (7 / 25) * (1 / a + 1 / b + 1 / c + 1 / (a + b + c)) ^ 2  :=  by sorry
