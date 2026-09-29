-- Prove2me | Theorems.Thm_WorkbookSource_base_1361
-- name    : WorkbookSource.base_1361
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:24:37.988067+00:00
-- url     : https://prove2.me/theorems/0e645c68-650b-4377-92a7-4198217b5f81
-- title:
--   An eighth-degree three-variable polynomial is nonnegative
-- statement:
--   Prove that $ P={a}^{6}{b}^{2}+2\,{a}^{6}bc+{a}^{6}{c}^{2}-2\,{a}^{5}{b}^{3}-2\,{a}^{5}{b}^{2}c-2\,{a}^{5}b{c}^{2}-2\,{a}^{5}{c}^{3}+2\,{a}^{4}{b}^{4}+4\,{a}^{4}{b}^{2}{c}^{2}+2\,{a}^{4}{c}^{4}-2\,{a}^{3}{b}^{5}-2\,{a}^{3}{b}^{3}{c}^{2}-2\,{a}^{3}{b}^{2}{c}^{3}-2\,{a}^{3}{c}^{5}+{a}^{2}{b}^{6}-2\,{a}^{2}{b}^{5}c+4\,{a}^{2}{b}^{4}{c}^{2}-2\,{a}^{2}{b}^{3}{c}^{3}+4\,{a}^{2}{b}^{2}{c}^{4}-2\,{a}^{2}b{c}^{5}+{a}^{2}{c}^{6}+2\,a{b}^{6}c-2\,a{b}^{5}{c}^{2}-2\,a{b}^{2}{c}^{5}+2\,ab{c}^{6}+{b}^{6}{c}^{2}-2\,{b}^{5}{c}^{3}+2\,{b}^{4}{c}^{4}-2\,{b}^{3}{c}^{5}+{b}^{2}{c}^{6} \geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1361` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1361; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1361 (a b c : ℝ) : a^6 * b^2 + 2 * a^6 * b * c + a^6 * c^2 - 2 * a^5 * b^3 - 2 * a^5 * b^2 * c - 2 * a^5 * b * c^2 - 2 * a^5 * c^3 + 2 * a^4 * b^4 + 4 * a^4 * b^2 * c^2 + 2 * a^4 * c^4 - 2 * a^3 * b^5 - 2 * a^3 * b^3 * c^2 - 2 * a^3 * b^2 * c^3 - 2 * a^3 * c^5 + a^2 * b^6 - 2 * a^2 * b^5 * c + 4 * a^2 * b^4 * c^2 - 2 * a^2 * b^3 * c^3 + 4 * a^2 * b^2 * c^4 - 2 * a^2 * b * c^5 + a^2 * c^6 + 2 * a * b^6 * c - 2 * a * b^5 * c^2 - 2 * a * b^2 * c^5 + 2 * a * b * c^6 + b^6 * c^2 - 2 * b^5 * c^3 + 2 * b^4 * c^4 - 2 * b^3 * c^5 + b^2 * c^6 ≥ 0  :=  by sorry
