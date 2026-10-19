-- Prove2me | Theorems.Thm_AbelianTargets_FixedSlots_halfGlue_joint_lipschitz
-- name    : AbelianTargets.FixedSlots.halfGlue_joint_lipschitz
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:41:12.537333+00:00
-- url     : https://prove2.me/theorems/f93a2558-b189-4c47-a6a3-9590d004906e
-- title:
--   Joint Lipschitz estimate for two square families glued at a seam
-- statement:
--   Let $Z$ be a metric space, $K,L\ge0$, and let $F,G:[0,1]^2\to Z$ be respectively $K$- and $L$-Lipschitz for the maximum product metric. Assume
--   $$
--   F(1,u)=G(0,u)\qquad(u\in[0,1]).
--   $$
--   Define the horizontally glued square family by
--   $$
--   Q(r,u)=
--   \begin{cases}
--   F(2r,u),&r\le\tfrac12,\\
--   G(2r-1,u),&r>\tfrac12.
--   \end{cases}
--   $$
--   Then
--   $$
--   \operatorname{Lip}(Q)\le4\max(K,L).
--   $$
--   The seam identity is required for every value of the second parameter.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2.5 and 4, finite homotopy gluing supporting Lemma 4.1; https://arxiv.org/html/2609.39824v1#S4. Auxiliary formalization result in original module AbelianTargets/RectangleHalfGluing.lean, authoritative declaration span lines 44-81, SHA-256 d6cf8cc0c2770b241347a4110d8bd77cc2659855ede860843223993f68f2780a. Frozen original source is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_RectangleHalfGluing
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
end AbelianTargets.FixedSlots
open AbelianTargets
open AbelianTargets.FixedSlots
open scoped NNReal
variable {Z : Type*} [MetricSpace Z]

theorem AbelianTargets.FixedSlots.halfGlue_joint_lipschitz (F G : unitInterval × unitInterval → Z) {K L : ℝ≥0}
    (hF : LipschitzWith K F) (hG : LipschitzWith L G)
    (hmatch : ∀ u, F (1,u) = G (0,u)) : LipschitzWith (4*max K L) (halfGlue F G) := by sorry
