-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.finite_totient_block
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:54:03.374681+00:00
-- url     : https://prove2.me/submissions/39d899cc-e9d3-453b-938d-de4543737384

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_WeightedFloorBlocksR12
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
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
theorem solution (N : ℕ) (lo hi : ℝ) (h : lo ≤ hi) :
    (∑ l ∈ Finset.Icc 1 N,
      if lo < (l : ℝ) ∧ (l : ℝ) ≤ hi then (l.totient : ℤ) else 0) =
      finiteTotientPrefix N hi - finiteTotientPrefix N lo := by
  classical
  unfold finiteTotientPrefix
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hlo : (l : ℝ) ≤ lo
  · have hhi : (l : ℝ) ≤ hi := hlo.trans h
    simp [hlo, hhi, not_lt_of_ge hlo]
  · have hlo' : lo < (l : ℝ) := lt_of_not_ge hlo
    by_cases hhi : (l : ℝ) ≤ hi <;> simp [hlo, hlo', hhi]
