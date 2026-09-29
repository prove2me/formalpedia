-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_lowerDensityAtLeast_iff_of_eventual_iff
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.lowerDensityAtLeast_iff_of_eventual_iff
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:14:54.132442+00:00
-- url     : https://prove2.me/theorems/b1632ca9-c2f0-4255-a75f-19ec24d4af2d
-- title:
--   Lean source theorem: lowerDensityAtLeast_iff_of_eventual_iff
-- statement:
--   If two sets of natural numbers agree on membership from T onward, then they satisfy exactly the same lower-density-at-least-d bounds for every real d.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/DensityTransport.lean#L58-L67
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.lowerDensityAtLeast_iff_of_eventual_iff (E F : Set ℕ) (T : ℕ) (d : ℝ)
    (heq : ∀ n, T ≤ n → (n ∈ E ↔ n ∈ F)) :
    LowerDensityAtLeast E d ↔ LowerDensityAtLeast F d := by sorry
