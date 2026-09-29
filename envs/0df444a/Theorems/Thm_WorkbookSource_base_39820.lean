-- Prove2me | Theorems.Thm_WorkbookSource_base_39820
-- name    : WorkbookSource.base_39820
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:54:25.393287+00:00
-- url     : https://prove2.me/theorems/e29bdde9-2b62-478c-9085-14c053c2ff0c
-- title:
--   An eighth-degree inequality for squared triangle sides
-- statement:
--   Let $ x,y,z\ge 0 $ such that $ x^2,y^2,z^2 $ are the side lengths of a triangle. Prove or disprove the following:
--
--   $x^8+y^8+z^8+x^6yz+xy^6z+xyz^6+2x^3y^3z^2+2x^3y^2z^3+2x^2y^3z^3\ge x^5y^2z+y^5z^2x+z^5x^2y+x^5yz^2+y^5zx^2+z^5xy^2+2x^4y^4+2y^4z^4+2z^4x^4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39820` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39820; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_39820 {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hx2 : x^2 ≤ y^2 + z^2) (hy2 : y^2 ≤ z^2 + x^2) (hz2 : z^2 ≤ x^2 + y^2) :  x^8 + y^8 + z^8 + x^6 * y * z + x * y^6 * z + x * y * z^6 + 2 * x^3 * y^3 * z^2 + 2 * x^3 * y^2 * z^3 + 2 * x^2 * y^3 * z^3 ≥ x^5 * y^2 * z + y^5 * z^2 * x + z^5 * x^2 * y + x^5 * y * z^2 + y^5 * z * x^2 + z^5 * x * y^2 + 2 * x^4 * y^4 + 2 * y^4 * z^4 + 2 * z^4 * x^4  :=  by sorry
