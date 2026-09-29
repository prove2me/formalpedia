-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_finite_totient_block
-- name    : ErdosProblems.Erdos1049.PaperR12.finite_totient_block
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:53:57.838151+00:00
-- url     : https://prove2.me/theorems/5806edef-5a81-4814-bd5d-94801615bcb7
-- title:
--   Finite totient block
-- statement:
--   For natural N and real lo≤hi, the totient sum over 1≤ℓ≤N satisfying lo<ℓ≤hi equals finiteTotientPrefix(N,hi)−finiteTotientPrefix(N,lo).
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/WeightedFloorBlocksR12.lean#L127-L141
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

theorem ErdosProblems.Erdos1049.PaperR12.finite_totient_block (N : ℕ) (lo hi : ℝ) (h : lo ≤ hi) :
    (∑ l ∈ Finset.Icc 1 N,
      if lo < (l : ℝ) ∧ (l : ℝ) ≤ hi then (l.totient : ℤ) else 0) =
      finiteTotientPrefix N hi - finiteTotientPrefix N lo := by sorry
