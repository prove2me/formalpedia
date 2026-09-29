-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_LowerDensityAtLeast_of_eventual_subset
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.LowerDensityAtLeast.of_eventual_subset
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T20:23:24.699381+00:00
-- url     : https://prove2.me/theorems/8f1d9611-69a9-4687-ab25-ee134e4a8dad
-- title:
--   Transfer a lower-density bound through eventual containment
-- statement:
--   If E has lower-density bound d and every member of E from some index T onward belongs to F, then F has the same lower-density bound.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/DensityTransport.lean#L39-L56
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.LowerDensityAtLeast.of_eventual_subset {E F : Set ℕ} {d : ℝ}
    (hE : LowerDensityAtLeast E d) (T : ℕ)
    (hsub : ∀ n, T ≤ n → n ∈ E → n ∈ F) : LowerDensityAtLeast F d := by sorry
