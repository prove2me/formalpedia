-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.actual_reciprocal_totient_block
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:59:28.850243+00:00
-- url     : https://prove2.me/submissions/f624c8dc-00c0-4316-87cc-3736e5c7b100

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_WeightedFloorBlocksR12
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_finite_totient_block
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
theorem solution (N : ℕ) (n k u v : ℝ)
    (hn : 0 ≤ n) (hk : 0 ≤ k) (hu : 0 < u) (huv : u < v) :
    (∑ l ∈ Finset.Icc 1 N,
      if n / (k + v) < (l : ℝ) ∧ (l : ℝ) ≤ n / (k + u)
      then (l.totient : ℤ) else 0) =
      finiteTotientPrefix N (n / (k + u)) -
        finiteTotientPrefix N (n / (k + v)) := by
  apply finite_totient_block
  exact div_le_div_of_nonneg_left hn (by linarith) (by linarith)
