-- Prove2me | Definitions.Def_AT260939824_RectangleHalfGluing
-- name    : AT260939824_RectangleHalfGluing
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:54:54.680999+00:00
-- url     : https://prove2.me/theorems/41a35774-8e74-4b7f-8a6b-a96a24349c4e
-- title:
--   Half-rectangle gluing of two path families
-- statement:
--   For any set $Z$ and maps $F,G:[0,1]^2\to Z$, define a family on the doubled horizontal rectangle by
--   $$\operatorname{halfGlue}(F,G)(r,t)=
--   \begin{cases}F(2r,t)&r\le1/2,\\G(2r-1,t)&r>1/2.\end{cases}$$
--   A raw version allows $r\in\mathbb R$ by clamping each rescaled parameter to $[0,1]$. If both families take values in $S\subseteq Z$, so does the glued family. No seam equality or topology is needed for this definition or membership statement; matching seams are used by subsequent continuity and metric lemmas.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/RectangleHalfGluing.lean, selected declaration lines 11-13, 15-16, 83-89, 91-92, 94-95; SHA-256 d6cf8cc0c2770b241347a4110d8bd77cc2659855ede860843223993f68f2780a. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_VariableRowFamilies
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

/-! Literal seam gluing of two square families, including moving endpoints. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section

variable {Z : Type*} [MetricSpace Z]

def halfGlueRaw (F G : unitInterval × unitInterval → Z) (z : ℝ × unitInterval) : Z :=
  if z.1 ≤ 1/2 then F (clampInterval (2*z.1),z.2)
  else G (clampInterval (2*z.1-1),z.2)

def halfGlue (F G : unitInterval × unitInterval → Z) (z : unitInterval × unitInterval) : Z :=
  halfGlueRaw F G (z.1,z.2)







theorem halfGlue_mem {S : Set Z} (F G : unitInterval × unitInterval → Z)
    (hF : ∀ z, F z ∈ S) (hG : ∀ z, G z ∈ S) (z : unitInterval × unitInterval) :
    halfGlue F G z ∈ S := by
  unfold halfGlue halfGlueRaw
  split
  · exact hF _
  · exact hG _

@[simp] theorem halfGlue_zero (F G : unitInterval × unitInterval → Z) (u : unitInterval) :
    halfGlue F G (0,u) = F (0,u) := by simp [halfGlue,halfGlueRaw,clampInterval]

@[simp] theorem halfGlue_one (F G : unitInterval × unitInterval → Z) (u : unitInterval) :
    halfGlue F G (1,u) = G (1,u) := by norm_num [halfGlue,halfGlueRaw,clampInterval]

end
end AbelianTargets.FixedSlots


