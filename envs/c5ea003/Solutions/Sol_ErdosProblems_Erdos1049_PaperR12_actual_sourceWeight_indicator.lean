-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.actual_sourceWeight_indicator
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:00:29.018996+00:00
-- url     : https://prove2.me/submissions/8d5d9756-5c91-4d5d-8c5f-8a732519362d

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_WeightedFloorBlocksR12
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR11_omegaWeight_fract
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR7_omega_indicator
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic

namespace PaperR11
end PaperR11

/-!
# Exact weighted floor blocks for the actual thirteen intervals

Rewrites the weighted totient sum as thirteen reciprocal floor blocks.
The lower reciprocal endpoint is strict and the upper one weak. This file
constructs the literal finite weighted sums and identifies each block with
a difference of totient prefixes. It does not label this finite identity as
an asymptotic estimate or assume a summatory-totient error bound.
-/

namespace ErdosProblems.Erdos1049.PaperR12
open PaperR11
open scoped BigOperators
end ErdosProblems.Erdos1049.PaperR12

open PaperR11
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
open Classical in

theorem solution (n l : ℕ) :
    sourceWeight n l =
      if PaperR7.InOmegaSupport (Int.fract ((n : ℝ) / l)) then 1 else 0 := by
  classical
  have hi := PaperR7.omega_indicator (Int.fract ((n : ℝ) / l))
    (Int.fract_nonneg _) (Int.fract_lt_one _)
  have hw : sourceWeight n l = PaperR7.omegaWeight (Int.fract ((n : ℝ) / l)) := by
    exact (omegaWeight_fract _).symm
  rw [hw]
  by_cases hs : PaperR7.InOmegaSupport (Int.fract ((n : ℝ) / l))
  · rw [if_pos hs]
    exact hi.2.mpr hs
  · rw [if_neg hs]
    rcases hi.1 with h | h
    · exact h
    · exact (hs (hi.2.mp h)).elim
