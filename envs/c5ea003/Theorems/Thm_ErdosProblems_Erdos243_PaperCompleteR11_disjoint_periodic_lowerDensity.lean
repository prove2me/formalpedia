-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_disjoint_periodic_lowerDensity
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.disjoint_periodic_lowerDensity
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:36:46.989322+00:00
-- url     : https://prove2.me/theorems/6c99fcdb-68a9-4a0e-9839-1f3a15cb126e
-- title:
--   Lean source theorem: disjoint_periodic_lowerDensity
-- statement:
--   If every length-L window starting at r+sk contains an element of E, with s>0 and L≤s, then E has lower density at least 1/s.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/DensityTransport.lean#L69-L80
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.disjoint_periodic_lowerDensity (E : Set ℕ) (r s L : ℕ)
    (hs : 0 < s) (hL : L ≤ s)
    (hhit : ∀ k : ℕ, ∃ i : ℕ, i < L ∧ r + s * k + i ∈ E) :
    LowerDensityAtLeast E (1 / (s : ℝ)) := by sorry
