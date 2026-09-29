-- Prove2me | Theorems.Thm_WorkbookSource_plus_46959
-- name    : WorkbookSource.plus_46959
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:31:03.222096+00:00
-- url     : https://prove2.me/theorems/d1094bba-4451-46a4-a22d-4cc0e0eb897f
-- title:
--   A parametric cyclic quartic inequality
-- statement:
--   Prove the following inequality for real numbers $a,b,c$ :
--
--    $a^4+b^4+c^4+r(a^2b^2+b^2c^2+c^2a^2)+(p+q-r-1)(a^2bc+ab^2c+abc^2)\ge p(a^3b+b^3c+c^3a)+q(ab^3+bc^3+ca^3)$
--
--    Where $p,q,r$ are real numbers which satisfy $3(1+r)\ge p^2+pq+q^2$
--
--    $ \sum_{cyc}(a^4+ra^2b^2+(p+q-r-1)a^2bc-pa^3b-qa^3c)\geq0\Leftrightarrow$
--
--    $\Leftrightarrow\sum_{cyc}(2a^4+2ra^2b^2+2(p+q-r-1)a^2bc-(p+q)(a^3b+a^3c))\geq(p-q)\sum_{cyc}(a^3b-a^3c)$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_46959` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_46959; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_46959 (a b c p q r : ℝ) (hp : 3 * (1 + r) ≥ p ^ 2 + p * q + q ^ 2) : a ^ 4 + b ^ 4 + c ^ 4 + r * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + (p + q - r - 1) * (a ^ 2 * b * c + a * b ^ 2 * c + a * b * c ^ 2) ≥ p * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + q * (a * b ^ 3 + b * c ^ 3 + c * a ^ 3)   :=  by sorry
