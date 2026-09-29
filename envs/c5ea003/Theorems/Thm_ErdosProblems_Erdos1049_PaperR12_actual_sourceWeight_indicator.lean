-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_actual_sourceWeight_indicator
-- name    : ErdosProblems.Erdos1049.PaperR12.actual_sourceWeight_indicator
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T19:00:22.013976+00:00
-- url     : https://prove2.me/theorems/33733f91-efb7-49b7-8588-47a358321d84
-- title:
--   Actual source weight indicator
-- statement:
--   For all natural n,ℓ, sourceWeight(n,ℓ) is 1 exactly when the fractional part of n/ℓ is in the defined omega support, and is 0 otherwise.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/WeightedFloorBlocksR12.lean#L83-L100
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_WeightedFloorBlocksR12
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
open PaperR11
open scoped BigOperators

open ErdosProblems.Erdos1049.PaperR12

open ErdosProblems.Erdos1049.PaperR11

open Classical in

theorem ErdosProblems.Erdos1049.PaperR12.actual_sourceWeight_indicator (n l : ℕ) :
    sourceWeight n l =
      if PaperR7.InOmegaSupport (Int.fract ((n : ℝ) / l)) then 1 else 0 := by sorry
