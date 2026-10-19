-- Prove2me | Definitions.Def_AT260939824_OneHeightRetraction
-- name    : AT260939824_OneHeightRetraction
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:18:38.263189+00:00
-- url     : https://prove2.me/theorems/9fc99e71-d28a-4cca-ab2a-51178660eadf
-- title:
--   Retraction to the next lower carrier
-- statement:
--   For base $m\ge1$, the terminal state of the one-layer deformation has support in height at most $K$. Restricting its coordinates gives a retraction from the carrier at height $K+1$ to the carrier at height $K$. The deformation fixes points already in the lower carrier and preserves bottom points, and the bundle records the joint regularity needed to iterate the construction.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/OneHeightRetraction.lean, selected declaration lines 11-21, 23-28, 30-32, 34-36, 38-48, 54-62; SHA-256 4c859a5a20a7a29cd59ef3d438dd27939f9d267090eb0763b228371e91a91ced. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierCollapseFixed
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierHeightCut
import Definitions.Def_AT260939824_CarrierNesting
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ControlledStages
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_LowerCarrierCollapse
import Definitions.Def_AT260939824_OneHeightDeformation
import Definitions.Def_AT260939824_ParallelCollapse
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleCollapse
import Definitions.Def_AT260939824_UpperCarrierCollapse
import Definitions.Def_AT260939824_VerticalCarrierCollapse
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

set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section

theorem oneHeightStage_fixes_lower {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Probability (CarrierVertex (K+1) A B)) (hp : ∀ v, 0 < p.mass v → v.1.2 ≤ K)
    (n : ℕ) (t : unitInterval) : oneHeightStage hm n (p,t) = p := by
  cases n with
  | zero => exact top_mapList_fixes_lower hm p hp _ t
  | succ n =>
    simp only [oneHeightStage]
    split_ifs
    · exact fan_mapList_fixes_lower hm _ p hp _ t
    · exact verticalMap_fixes_lower p hp t
    · rfl

theorem oneHeightHomotopy_fixes_lower {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m (K+1) A B) (hp : ∀ v, 0 < p.1.mass v → v.1.2 ≤ K)
    (t : unitInterval) : oneHeightHomotopy hm p t = p := by
  apply Subtype.ext
  exact stageCurve_fixed (fun p : Realization m (K+1) A B => p.1) (oneHeightStage hm)
    p p.1 rfl (fun n t => oneHeightStage_fixes_lower hm p.1 hp n t) (m+2) t

def oneHeightRetraction {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B) :
    Realization m K A B :=
  restrictHeight hm (oneHeightHomotopy hm p 1) (oneHeightHomotopy_one_height hm p)

theorem include_oneHeightRetraction {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B) :
    carrierInclude (by omega : K ≤ K+1) (oneHeightRetraction hm p) = oneHeightHomotopy hm p 1 :=
  include_restrictHeight hm _ _

theorem oneHeightRetraction_joint {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) :
    ∃ J : ℝ≥0, LipschitzWith J (oneHeightRetraction (K := K) (A := A) (B := B) hm) := by
  obtain ⟨J,hJ⟩ := oneHeightHomotopy_joint (K := K) (A := A) (B := B) hm
  refine ⟨J,LipschitzWith.of_dist_le_mul ?_⟩
  intro p q
  have hd : dist (oneHeightRetraction hm p) (oneHeightRetraction hm q) =
      dist (oneHeightHomotopy hm p 1) (oneHeightHomotopy hm q 1) := by
    rw [←include_oneHeightRetraction hm p,←include_oneHeightRetraction hm q]
    exact ((isometry_include (m := m) (A := A) (B := B) (by omega : K ≤ K+1)).dist_eq _ _).symm
  rw [hd]
  simpa only [Prod.dist_eq,dist_self,max_eq_left dist_nonneg] using hJ.dist_le_mul (p,1) (q,1)



theorem oneHeightRetraction_preserves_bottom {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m (K+1) A B) (hp : ∀ v, 0 < p.1.mass v → v.1.2 = 0)
    (v : CarrierVertex K A B) (hv : 0 < (oneHeightRetraction hm p).1.mass v) : v.1.2 = 0 := by
  have hpl : ∀ u, 0 < p.1.mass u → u.1.2 ≤ K := fun u hu => by rw [hp u hu]; exact Nat.zero_le _
  change 0 < (Probability.push vertexLower (oneHeightHomotopy hm p 1).1).mass v at hv
  rw [oneHeightHomotopy_fixes_lower hm p hpl 1] at hv
  obtain ⟨u,hu,hup⟩ := (Probability.push_pos_iff vertexLower p.1 v).mp hv
  rw [←hu]
  simp only [vertexLower,hp u hup,Nat.zero_min]

end
end AbelianTargets.IntervalCarriers


