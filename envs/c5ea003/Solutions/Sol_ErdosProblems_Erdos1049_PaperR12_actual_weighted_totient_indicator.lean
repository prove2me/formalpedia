-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.actual_weighted_totient_indicator
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:04:16.65997+00:00
-- url     : https://prove2.me/submissions/4586c715-7be2-47c8-940a-574a11e923f5

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_WeightedFloorBlocksR12
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_actual_sourceWeight_indicator
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







theorem omegaSupport_iff_sourceIntervals (x : ℝ) :
    PaperR7.InOmegaSupport x ↔
      ∃ uv ∈ sourceIntervals, (uv.1 : ℝ) ≤ x ∧ x < (uv.2 : ℝ) := by
  norm_num [sourceIntervals, PaperR7.InOmegaSupport]
end ErdosProblems.Erdos1049.PaperR12

open PaperR11
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution (n : ℕ) :
    actualWeightedTotientSum n =
      ∑ l ∈ Finset.Icc 1 (15 * n),
        if ∃ uv ∈ sourceIntervals,
          (uv.1 : ℝ) ≤ Int.fract ((n : ℝ) / l) ∧
          Int.fract ((n : ℝ) / l) < (uv.2 : ℝ)
        then (l.totient : ℤ) else 0 := by
  classical
  unfold actualWeightedTotientSum
  apply Finset.sum_congr rfl
  intro l hl
  rw [actual_sourceWeight_indicator, omegaSupport_iff_sourceIntervals]
  split_ifs <;> simp
