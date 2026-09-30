-- Prove2me | Theorems.Thm_Fin_apply_le_last_add_sum_max_sub
-- name    : Fin.apply_le_last_add_sum_max_sub
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-29T19:14:45.649298+00:00
-- url     : https://prove2.me/theorems/8a658e5b-aae2-472a-9dc5-870d2820fe3b
-- title:
--   Finite sequence bounded by last value plus positive increments
-- statement:
--   Let $n$ be a natural number and $f$ a real-valued sequence on $\mathrm{Fin}(n+1)$. Write $\mathrm{last}\,n$ for the final index. Then for every index $i$,\n\n$$f(i)\le f(\mathrm{last}\,n)+\sum_{j\in\mathrm{Fin}\,n}\max(f(j.\mathrm{castSucc})-f(j.\mathrm{succ}),0).$$\n\nEach term bounds the positive backward increment; the sum telescopes to control the drop from the endpoint. This discrete Gronwall-type estimate is reused in polygon height bounds.\n\n**Formalization Note** Drift repair: upstream imports `Mathlib.Basic.Real.Basic` (present in v4.35, absent in the supported rev); here replaced by `Mathlib.Data.Real.Basic` with identical content.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Algebra/Order/Fin.lean#L11-L12

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
open Fin

namespace Fin

theorem apply_le_last_add_sum_max_sub {n : ℕ} (f : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : f i ≤ f (Fin.last n) + ∑ j : Fin n, max (f j.castSucc - f j.succ) 0 := by sorry

end Fin
