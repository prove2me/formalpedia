-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_exceptionCount_le_of_eventual_subset
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.exceptionCount_le_of_eventual_subset
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T20:22:49.43293+00:00
-- url     : https://prove2.me/theorems/ac3fb114-09f3-4e73-b5e7-6b2d3a54736c
-- title:
--   Exception-count bound for eventual containment
-- statement:
--   If every member of E from index T onward belongs to F, then the count of E below X is at most T plus the count of F below X.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/DensityTransport.lean#L21-L37
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.exceptionCount_le_of_eventual_subset (E F : Set ℕ) (T X : ℕ)
    (hsub : ∀ n, T ≤ n → n ∈ E → n ∈ F) :
    exceptionCount E X ≤ T + exceptionCount F X := by sorry
