-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_WeightedFloorBlocksR12
-- name    : ErdosProblems_Erdos1049_WeightedFloorBlocksR12
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:47:24.171696+00:00
-- url     : https://prove2.me/theorems/2101a792-dce2-4bcd-9d17-585673e14ac0
-- title:
--   Exact weighted floor blocks for the actual thirteen intervals
-- statement:
--   Each literal source interval becomes a reciprocal floor block with strict lower and weak upper boundary, converting the finite weighted totient sum to prefix differences. The submitted module contains the source declarations sourceIntervals, sourceIntervals_card, sourceIntervals_bounds, omegaSupport_iff_sourceIntervals, reciprocal_block_iff, among others. Source topic: Exact weighted floor blocks for the actual thirteen intervals.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/WeightedFloorBlocksR12.lean#L17-L171
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
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

/-- The thirteen rational half-open intervals, not a replacement support. -/
def sourceIntervals : Finset (ℚ × ℚ) :=
  {(1/14, 1/12), (1/7, 1/6), (3/14, 1/4), (2/7, 1/3),
   (5/14, 2/5), (3/7, 7/15), (1/2, 8/15), (4/7, 3/5),
   (9/14, 2/3), (5/7, 11/15), (11/14, 4/5),
   (6/7, 13/15), (13/14, 14/15)}















/-- A finite totient prefix retains the exact integer cut-off. -/
noncomputable def finiteTotientPrefix (N : ℕ) (x : ℝ) : ℤ :=
  ∑ l ∈ Finset.Icc 1 N, if (l : ℝ) ≤ x then (l.totient : ℤ) else 0





noncomputable def actualWeightedTotientSum (n : ℕ) : ℤ :=
  ∑ l ∈ Finset.Icc 1 (15 * n), sourceWeight n l * (l.totient : ℤ)



end ErdosProblems.Erdos1049.PaperR12


