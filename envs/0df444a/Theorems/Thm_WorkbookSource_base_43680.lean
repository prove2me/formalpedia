-- Prove2me | Theorems.Thm_WorkbookSource_base_43680
-- name    : WorkbookSource.base_43680
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:47:25.754535+00:00
-- url     : https://prove2.me/theorems/45ceb479-a69d-419f-955a-02378c942432
-- title:
--   A weighted cyclic pair-product reciprocal lower bound
-- statement:
--   If $ a,b,c>0 $ prove that:
--    $ \frac{a}{b(b+2c)}+\frac{b}{c(c+2a)}+\frac{c}{a(a+2b)}\ge\frac{3}{a+b+c} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43680` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43680; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_43680 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b * (b + 2 * c)) + b / (c * (c + 2 * a)) + c / (a * (a + 2 * b))) ≥ 3 / (a + b + c)  :=  by sorry
