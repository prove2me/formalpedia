-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_zeroLowerDensity_iff_no_positive_lower_bound
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.zeroLowerDensity_iff_no_positive_lower_bound
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:26:33.482693+00:00
-- url     : https://prove2.me/theorems/57f87644-e9cc-4289-9b3f-d725ed2b7bc0
-- title:
--   Lean source theorem: zeroLowerDensity_iff_no_positive_lower_bound
-- statement:
--   A set of natural numbers has zero lower density exactly when it has no strictly positive lower-density-at-least bound.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicZeroDensityShape.lean#L33-L52
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring

/-!
# The complete zero-lower-density primitive-shape reduction

The manuscript's primitive-shape lemma is stated
under zero lower density, not under the universal positive threshold. Its
unit-constant conclusion is proved here at exactly that hypothesis.
The arbitrary positive-threshold theorem must not reuse that conclusion.
-/


open ErdosProblems.Erdos243.PaperCompleteR9

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.zeroLowerDensity_iff_no_positive_lower_bound (E : Set ℕ) :
    ZeroLowerDensity E ↔ ∀ d : ℝ, 0 < d → ¬ LowerDensityAtLeast E d := by sorry
