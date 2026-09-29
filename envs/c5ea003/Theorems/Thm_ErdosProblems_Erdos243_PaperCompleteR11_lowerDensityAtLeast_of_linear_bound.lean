-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_lowerDensityAtLeast_of_linear_bound
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.lowerDensityAtLeast_of_linear_bound
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T20:34:52.610177+00:00
-- url     : https://prove2.me/theorems/13e917d6-12f0-4774-8613-4a80b2f1355f
-- title:
--   Lower-density bound from a linear exception-count inequality
-- statement:
--   If b is positive and aX ≤ b times the exception count of E below X plus c for every natural X, then E satisfies LowerDensityAtLeast(E,a/b).
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/WindowIncidence.lean#L130-L154
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

/-!
# Window incidences and quantitative exceptional density

Every hit is charged to an exceptional index together
with its offset. Overlapping windows therefore cost at most their length, not
the number of residue classes. No density assumption is hidden in the counting
lemmas. `LowerDensityAtLeast` uses the usual epsilon / eventual-prefix definition
of a lower bound for the lower asymptotic density (prefixes start at zero).
-/


open ErdosProblems.Erdos243.PaperCompleteR9

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.lowerDensityAtLeast_of_linear_bound (E : Set ℕ) (a b c : ℝ)
    (hb : 0 < b)
    (h : ∀ X : ℕ, a * (X : ℝ) ≤ b * (exceptionCount E X : ℝ) + c) :
    LowerDensityAtLeast E (a / b) := by sorry
