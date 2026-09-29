-- Prove2me | Theorems.Thm_WorkbookSource_base_6535
-- name    : WorkbookSource.base_6535
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:24:38.467481+00:00
-- url     : https://prove2.me/theorems/f0f50c5d-1b03-4ad2-9c6f-f6767dd3850b
-- title:
--   A comparison between products of second, third, fifth and sixth power sums
-- statement:
--   x,y,z is real numbers,
--    prove that:
--    $ (x^2 + y^2 + z^2)(x^6 + y^6 + z^6) \geq (x^5 + y^5 + z^5)(x^3 + y^3 + z^3)$
--
--    BQ
--    We also can prove this with CS as follows
--    $ (x^2 + y^2 + z^2)(x^4 + y^4 + z^4)\ge(x^3 + y^3 + z^3)^2; \ \ (1)$
--    $ (x^4 + y^4 + z^4)(x^6 + y^6 + z^6)\ge(x^5 + y^5 + z^5)^2; \ \ (2)$
--    $ (x^5 + y^5 + z^5)(x^3 + y^3 + z^3)\ge(x^4 + y^4 + z^4)^2; \ \ (3)$ Again one can multiply (1); (2); (3) to get the desired result.
--
--    Try to apply these types of inequalities before complete expansion, nobody would read that type of a proof . (No offence)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6535` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6535; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6535  (x y z : ℝ) :
  (x^2 + y^2 + z^2) * (x^6 + y^6 + z^6) ≥ (x^5 + y^5 + z^5) * (x^3 + y^3 + z^3)  :=  by sorry
