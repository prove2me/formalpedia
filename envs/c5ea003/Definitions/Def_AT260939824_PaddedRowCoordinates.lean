-- Prove2me | Definitions.Def_AT260939824_PaddedRowCoordinates
-- name    : AT260939824_PaddedRowCoordinates
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:09:28.04356+00:00
-- url     : https://prove2.me/theorems/a1b416d8-b144-42da-ad05-f674c02f889b
-- title:
--   Coordinates of endpoint-padded rows
-- statement:
--   A finite list of vertices is extended to a common length by repeating its chosen endpoint. This bundle records exact values of the padded list at every index, including indices beyond the original list and the seam after appending one edge. These identities identify the literal piecewise affine paths of padded rows without changing their slot conventions.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/PaddedRowCoordinates.lean, selected declaration lines 8-15, 17-23, 25-33; SHA-256 d07d260161dd5bddfde543f1f8ae61af72cb7fa6bd364a9c142cef4d16952512. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_FixedSlotPadding
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_JointCarrierRows
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_WordPathHelpers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

/-! Coordinate identities for canonical endpoint padding and one appended edge. -/

namespace AbelianTargets
variable {V : Type*} [DecidableEq V]

theorem padRow_getD (N : ℕ) (z : V) (w : List V) (j : ℕ) :
    (padRow N z w).getD j z = w.getD j z := by
  simp only [padRow,List.getD_eq_getElem?_getD,List.getElem?_append]
  split_ifs with hj
  · rfl
  · rw [List.getElem?_eq_none (l := w) (i := j) (by omega)]
    simp only [List.getElem?_replicate,Option.getD_none]
    split <;> rfl

theorem list_getD_terminal {w : List V} {p : V} (hz : w.getLast? = some p)
    (j : ℕ) (hj : w.length-1 ≤ j) : w.getD j p = p := by
  by_cases hj' : j < w.length
  · have he : j = w.length-1 := by omega
    simp only [List.getD_eq_getElem?_getD,he,←List.getLast?_eq_getElem?,hz,Option.getD_some]
  · simp only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (l := w) (i := j) (by omega),Option.getD_none]

theorem getD_append_endpoint (w : List V) (p q : V) (j : ℕ) :
    (w++[q]).getD j q = if j < w.length then w.getD j p else q := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append]
  by_cases hj : j < w.length
  · rw [if_pos hj,if_pos hj]
    rw [List.getElem?_eq_getElem hj]
    rfl
  · rw [if_neg hj,if_neg hj]
    cases j-w.length <;> rfl

end AbelianTargets


