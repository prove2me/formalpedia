-- Prove2me | Theorems.Thm_Convex_smul_mem_of_nonneg_of_le
-- name    : Convex.smul_mem_of_nonneg_of_le
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T13:37:01.614918+00:00
-- url     : https://prove2.me/theorems/53a274b2-b39e-4025-b892-44a2177fec11
-- title:
--   Convex segment from the origin stays inside
-- statement:
--   In a convex set containing $0$ and $a\cdot v$, every $x\cdot v$ with $0\le x\le a$ stays inside: write it as $(x/a)\cdot(a\cdot v)$ with ratio in $[0,1]$. Drift repair: `Mathlib.Basic.Real.Basic` replaced by `Mathlib.Data.Real.Basic`.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/Convex/Basic.lean#L8-L19

import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
open Convex

namespace Convex

theorem smul_mem_of_nonneg_of_le {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E} (hs : Convex ℝ s) {v : E} {x a : ℝ} (hzero : (0 : E) ∈ s) (ha : a • v ∈ s) (hx : 0 ≤ x) (hxa : x ≤ a) : x • v ∈ s := by sorry

end Convex
