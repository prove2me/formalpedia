-- Prove2me | Definitions.Def_AT260939824_FixedRowRealization
-- name    : AT260939824_FixedRowRealization
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:00:23.426447+00:00
-- url     : https://prove2.me/theorems/d1d90a85-59b2-490d-bdd7-4979f511c6f5
-- title:
--   Realization of common-slot row moves
-- statement:
--   Face-chart data assign convex subsets of a real normed space to admissible vertex faces, containing their vertex images and satisfying an edge bound. A chain of fixed-slot combinatorial row moves is then realized by an endpoint-fixed homotopy in the prescribed target set. Its path-time bound depends on the common slot budget and the edge bound, and the initial and final paths retain their literal row parametrizations.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/FixedRowRealization.lean, selected declaration lines 13-16, 20-37; SHA-256 c0f6e0483c750d3dbf35ecf9ea1d61038d0b4f3714f0210a7e0b393cda1d9d54. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CanonicalRows
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_RowValidity
import Definitions.Def_AT260939824_WordPathHelpers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/-! A complete realization of padded combinatorial row moves by endpoint-fixed
homotopies. The path-time constant depends only on the common slot budget. -/

namespace AbelianTargets

open scoped NNReal

variable {V E : Type*} [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Face : Finset V → Prop}

structure FaceCharts (Face : Finset V → Prop) (ι : V → E) (S : Set E) (Δ : ℝ≥0) : Prop where
  downward : FaceDownward Face
  chart : ∀ s, Face s → ∃ F : Set E, Convex ℝ F ∧ F ⊆ S ∧ ∀ v ∈ s, ι v ∈ F
  edge_bound : ∀ a b, Face {a,b} → dist (ι a) (ι b) ≤ Δ

namespace FixedSlots

theorem canonicalRow_homotopy_mem (ι : V → E) {n : ℕ} {x z : V} {w u : List V}
    (hx : w.head? = some x) (hz : w.getLast? = some z) (hw : w.length = n+2)
    (hx' : u.head? = some x) (hz' : u.getLast? = some z) (hu : u.length = n+2)
    {S : Set E} {Δ : ℝ≥0} (hc : FaceCharts Face ι S Δ)
    (hquad : ∀ j ≤ n, Face {w.getD j z,w.getD (j+1) z,u.getD j z,u.getD (j+1) z})
    (t : unitInterval × unitInterval) :
    ((canonicalRow ι n x z w hx hz hw).homotopy
      (canonicalRow ι n x z u hx' hz' hu)) t ∈ S := by
  let R := canonicalRow ι n x z w hx hz hw
  let T := canonicalRow ι n x z u hx' hz' hu
  change rowHomotopy R.vertices T.vertices n (R.source.trans T.source.symm)
    (R.target.trans T.target.symm) t ∈ S
  apply rowHomotopy_mem_charts R.vertices T.vertices n (R.source.trans T.source.symm)
    (R.target.trans T.target.symm) _ t
  intro j hj
  obtain ⟨F,hconv,hsub,hv⟩ := hc.chart _ (hquad j hj)
  refine ⟨F,hconv,hsub,?_,?_,?_,?_⟩ <;>
    apply hv <;> simp



end FixedSlots

end AbelianTargets


