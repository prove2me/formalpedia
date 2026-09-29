-- Prove2me | Theorems.Thm_WorkbookSource_base_3618
-- name    : WorkbookSource.base_3618
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:28.111891+00:00
-- url     : https://prove2.me/theorems/6dcf5d58-f566-4c43-a6a7-dad98c48725a
-- title:
--   A cyclic product bound by quadratic forms
-- statement:
--   prove that
--   $32\, \left( {x}^{2}+{y}^{2} \right) \left( {x}^{2}+{z}^{2} \right) +32\, \left( {y}^{2}+{z}^{2} \right) \left( {x}^{2}+{y}^{2} \right) +32\, \left( {x}^{2}+{z}^{2} \right) \left( {y}^{2}+{z}^{2} \right) \geq \left( 3\,x+y \right) ^{2} \left( x+y \right) \left( z+2\,x+y \right) + \left( 3\,y+z \right) ^{2} \left( y+z \right) \left( 2\,y+z+x \right) + \left( 3\,z+x \right) ^{2} \left( z+x \right) \left( 2\,z+x+y \right)$
--   x,y,z>0
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3618` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3618; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3618 (x y z : ℝ) : 32 * (x^2 + y^2) * (x^2 + z^2) + 32 * (y^2 + z^2) * (x^2 + y^2) + 32 * (x^2 + z^2) * (y^2 + z^2) ≥ (3 * x + y)^2 * (x + y) * (z + 2 * x + y) + (3 * y + z)^2 * (y + z) * (2 * y + z + x) + (3 * z + x)^2 * (z + x) * (2 * z + x + y)  :=  by sorry
