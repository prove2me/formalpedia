-- Prove2me | Theorems.Thm_lean_workbook_plus_27939
-- name    : lean_workbook_plus_27939
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/a6b9fdea-0287-4d70-b554-8b2b8802aa23
-- statement:
--   prove $f\left(a,b,c\right)\geq0$, where $f\left(a,b,c\right)=12a^{6}+31a^{5}b+4a^{5}c-38a^{4}b^{2}+9a^{4}bc+16a^{4}c^{2}-33a^{3}b^{3}-20a^{3}b^{2}c+61a^{3}bc^{2}-33a^{3}c^{3}+16a^{2}b^{4}+61a^{2}b^{3}c-126a^{2}b^{2}c^{2}-20a^{2}bc^{3}-38a^{2}c^{4}+4ab^{5}+9ab^{4}c-20ab^{3}c^{2}+61ab^{2}c^{3}+9abc^{4}+31ac^{5}+12b^{6}+31b^{5}c-38b^{4}c^{2}-33b^{3}c^{3}+16b^{2}c^{4}+4bc^{5}+12c^{6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27939 : ∀ a b c : ℝ, 12 * a ^ 6 + 31 * a ^ 5 * b + 4 * a ^ 5 * c - 38 * a ^ 4 * b ^ 2 + 9 * a ^ 4 * b * c + 16 * a ^ 4 * c ^ 2 - 33 * a ^ 3 * b ^ 3 - 20 * a ^ 3 * b ^ 2 * c + 61 * a ^ 3 * b * c ^ 2 - 33 * a ^ 3 * c ^ 3 + 16 * a ^ 2 * b ^ 4 + 61 * a ^ 2 * b ^ 3 * c - 126 * a ^ 2 * b ^ 2 * c ^ 2 - 20 * a ^ 2 * b * c ^ 3 - 38 * a ^ 2 * c ^ 4 + 4 * a * b ^ 5 + 9 * a * b ^ 4 * c - 20 * a * b ^ 3 * c ^ 2 + 61 * a * b ^ 2 * c ^ 3 + 9 * a * b * c ^ 4 + 31 * a * c ^ 5 + 12 * b ^ 6 + 31 * b ^ 5 * c - 38 * b ^ 4 * c ^ 2 - 33 * b ^ 3 * c ^ 3 + 16 * b ^ 2 * c ^ 4 + 4 * b * c ^ 5 + 12 * c ^ 6 ≥ 0   :=  by sorry
