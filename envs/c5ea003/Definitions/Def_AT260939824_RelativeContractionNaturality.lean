-- Prove2me | Definitions.Def_AT260939824_RelativeContractionNaturality
-- name    : AT260939824_RelativeContractionNaturality
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:18:46.75764+00:00
-- url     : https://prove2.me/theorems/5f9ba7ed-b435-4ecb-90cd-39d28f4db557
-- title:
--   Isometric transport of boundary path families
-- statement:
--   Let $E$ be a real normed vector space, $Z,W$ metric spaces, $p,q\in Z$, and $S,B\ge0$. A boundary path family assigns a path $P_v:p\to q$ to each unit vector $v\in E$, with path-time Lipschitz bound $S$ and Lipschitz dependence on $v$ with bound $B$ in the uniform path metric. For an isometric equivalence $e:Z\to W$, define its transport by
--   $$(e_*P)_v(t)=e(P_v(t)).$$
--   The transported paths run from $e(p)$ to $e(q)$ and retain exactly the same two bounds $S,B$. This is the path-family transport used by naturality of cone fillings. The selected contraction identities also state that for a controlled contraction $H$ on $Z$, its isometric transport satisfies $H^e(e(z),t)=e(H(z,t))$. The associated reversed short paths therefore satisfy $P^e_{e(q)}(t)=e(P_q(t))$, with the same track and joint bounds.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/RelativeContractionNaturality.lean, selected declaration lines 15-17, 19-21, 50-63; SHA-256 d90a58f3fc0155593f27d843d44a89a845559d42ee3b9ff11ab3424b3e8b7d39. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTranslationEquiv
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.Basic
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
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.Compact
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

/-! The literal relative homotopy and cone filling commute with isometric
transport. These equalities concern the actual formulas, including all
four path deformation stages and the radial extension. -/

namespace AbelianTargets.ControlledContraction
open scoped unitInterval NNReal
noncomputable section
variable {Z W : Type*} [MetricSpace Z] [MetricSpace W]
variable {p q : Z} {D J S B : ℝ≥0}
variable (H : ControlledContraction p D J) (e : Z ≃ᵢ W)

@[simp] theorem transport_map (z : Z) (t : I) :
    (H.transport e).map (e z,t)=e (H.map (z,t)) := by
  simp [transport]

@[simp] theorem transport_shortPath (u : I) :
    (H.transport e).shortPath (e q) u=e (H.shortPath q u) := by
  simp [shortPath,transport]











variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def BoundaryPathFamily.transport (F : BoundaryPathFamily (E := E) p q S B)
    (e : Z ≃ᵢ W) : BoundaryPathFamily (E := E) (e p) (e q) S B where
  path v := (F.path v).map e.continuous
  path_lipschitz v := by
    simpa only [Path.map_coe,Function.comp_def,one_mul] using
      e.isometry.lipschitz.comp (F.path_lipschitz v)
  transverse := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    apply (ContinuousMap.dist_le (mul_nonneg B.property dist_nonneg)).mpr
    intro r
    change dist (e (F.path v r)) (e (F.path w r)) ≤ _
    rw [e.isometry.dist_eq]
    exact (ContinuousMap.dist_apply_le_dist r).trans (F.transverse.dist_le_mul v w)



end
end AbelianTargets.ControlledContraction


