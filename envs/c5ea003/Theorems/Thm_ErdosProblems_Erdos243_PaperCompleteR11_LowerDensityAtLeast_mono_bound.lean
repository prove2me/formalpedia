-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_LowerDensityAtLeast_mono_bound
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.LowerDensityAtLeast.mono_bound
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T20:23:32.573984+00:00
-- url     : https://prove2.me/theorems/5de9a667-333e-446b-b57c-f955662579a4
-- title:
--   A lower-density bound implies every weaker bound
-- statement:
--   If a set E satisfies the predicate LowerDensityAtLeast(E,b) and a ≤ b, then it satisfies LowerDensityAtLeast(E,a).
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/DensityTransport.lean#L10-L19
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Mathlib
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Finite-prefix and constant transport for the literal
lower asymptotic density used throughout the R11 window arguments. -/


open ErdosProblems.Erdos243.PaperCompleteR9

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.LowerDensityAtLeast.mono_bound {E : Set ℕ} {a b : ℝ}
    (h : LowerDensityAtLeast E b) (hab : a ≤ b) : LowerDensityAtLeast E a := by sorry
