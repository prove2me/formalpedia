-- Prove2me | Theorems.Thm_ConvexOn_lt_on_Ico_of_lt_of_le
-- name    : ConvexOn.lt_on_Ico_of_lt_of_le
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T14:18:26.915676+00:00
-- url     : https://prove2.me/theorems/444a75ae-9baa-47ae-af25-7e339ab5b2dd
-- title:
--   Convex function below bound on half-open interval
-- statement:
--   A convex $f$ with $f(a)<c$, $f(b)\le c$ satisfies $f(t)<c$ on $[a,b)$. Write $t$ as a convex combination and use strictness from the left endpoint. Drift repair: `Basic.Real.Basic` replaced by `Data.Real.Basic`.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Convex/Function.lean#L9-L11

import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ConvexOn

theorem lt_on_Ico_of_lt_of_le {f : ℝ → ℝ} {a b t c : ℝ} (hf : ConvexOn ℝ (Set.Icc a b) f) (ha : f a < c) (hb : f b ≤ c) (hat : a ≤ t) (htb : t < b) : f t < c := by sorry

end ConvexOn
