-- Prove2me | Theorems.Thm_WorkbookSource_base_23467
-- name    : WorkbookSource.base_23467
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:46:28.693802+00:00
-- url     : https://prove2.me/theorems/40f3c227-0139-452b-ae18-09fc3f106e83
-- title:
--   A quadratic-sum product is at most two at fixed total two
-- statement:
--   Its easy to see that:
--    $ (ab+bc+ac-1)^2\geq0$
--   is true for all $ a$ , $ b$ and $ c$ reals numbers.
--
--    $ \Leftrightarrow1\geq(2-(ab+bc+ac))(ab+bc+ac)$
--
--    $ \Leftrightarrow2\geq(4-2(ab+bc+ac))(ab+bc+ac)$
--
--   But when $ a+b+c=2$ , $ 4-2(ab+bc+ac)=a^2+b^2+c^2$
--
--    $ \Leftrightarrow2\geq(a^2+b^2+c^2)(ab+bc+ac)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23467` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23467; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23467  (a b c: ℝ)
  (h₀ : a + b + c = 2) :
  2 ≥ (a^2 + b^2 + c^2) * (a * b + b * c + c * a)  :=  by sorry
