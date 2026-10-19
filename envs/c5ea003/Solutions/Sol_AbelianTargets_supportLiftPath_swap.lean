-- Prove2me | solution 1 for AbelianTargets.supportLiftPath_swap
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:13:13.187992+00:00
-- url     : https://prove2.me/submissions/6e0ca929-96bc-40c4-b2cc-b3f200d60a32

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_DoubleCoverSupport
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_TopologicalWalks
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.SupportGeometry
section
/-!
# Concrete probability support geometry

The space `SupportPair H` is the support space `𝒟(H)` in Lemma 6.2 of
arXiv:2609.39824.  Its shore swap is a free involution.  Convex interpolation
inside a fixed shore gives the graph-edge paths, and interpolation of both
shores gives the square filling for a four-walk.  These are actual continuous
maps, not assumptions about an auxiliary presentation complex.
-/

open scoped BigOperators unitInterval

namespace AbelianTargets

noncomputable section

namespace Probability

variable {V : Type*} [Fintype V]

attribute [local instance] Classical.propDecidable





















theorem mix_symm (p q : Probability V) (t : I) :
    mix p q (unitInterval.symm t) = mix q p t := by
  ext v
  simp only [mix_mass, unitInterval.coe_symm_eq]
  ring





















end Probability

variable {V : Type*} [Fintype V] (H : SimpleGraph V)















namespace SupportPair






































































































end SupportPair

end

end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.SupportPathClasses
section
/-!
# Path-class algebra of the support complex

The fixed-shore paths compose uniquely, reverse correctly, and commute
across every product of two simplex faces.  This is the concrete topological
square relation in Lemma 6.2 of arXiv:2609.39824.
-/

open scoped unitInterval

namespace AbelianTargets.SupportPair

noncomputable section

variable {V : Type*} [Fintype V] (H : SimpleGraph V)

theorem leftPath_symm {p r q : Probability V}
    (hp : Compatible H p q) (hr : Compatible H r q) :
    (leftPath H hp hr).symm = leftPath H hr hp := by
  apply Path.ext
  funext t
  apply Subtype.ext
  simp [leftPath, Path.symm, Probability.mix_symm]

theorem rightPath_symm {p q s : Probability V}
    (hq : Compatible H p q) (hs : Compatible H p s) :
    (rightPath H hq hs).symm = rightPath H hs hq := by
  apply Path.ext
  funext t
  apply Subtype.ext
  simp [rightPath, Path.symm, Probability.mix_symm]



theorem leftPath_map_swap {p r q : Probability V}
    (hp : Compatible H p q) (hr : Compatible H r q) :
    (leftPath H hp hr).map (continuous_swap H) =
      rightPath H (compatible_symm H hp) (compatible_symm H hr) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  rfl

theorem rightPath_map_swap {p q s : Probability V}
    (hq : Compatible H p q) (hs : Compatible H p s) :
    (rightPath H hq hs).map (continuous_swap H) =
      leftPath H (compatible_symm H hq) (compatible_symm H hs) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-cover edge routes are exactly equivariant under
shore swap, including their parametrization. -/
theorem doubleEdgePath_map_swap {u u' v v' : V}
    (hu : H.Adj u u') (huv : H.Adj u v) (hv : H.Adj v' v) :
    (doubleEdgePath H hu huv hv).map (continuous_swap H) =
      (doubleEdgePath H hv.symm huv.symm hu.symm).symm := by
  unfold doubleEdgePath
  rw [Path.map_trans, rightPath_map_swap H (compatible_dirac H hu) (compatible_dirac H huv),
    leftPath_map_swap H (compatible_dirac H huv) (compatible_dirac H hv),
    Path.trans_symm,
    leftPath_symm H (compatible_dirac H huv.symm) (compatible_dirac H hu.symm),
    rightPath_symm H (compatible_dirac H hv.symm) (compatible_dirac H huv.symm)]





































end

end AbelianTargets.SupportPair

end

-- Preserved source skeleton: AbelianTargets.DoubleCoverLifts
section
/-!
# Binary lifts of graph walks

Walks lift to the bipartite double cover with the sheet determined by their
length parity.  This is the combinatorial covering step in Lemma 6.2.
-/

namespace AbelianTargets

variable {V : Type*} (H : SimpleGraph V)






















namespace ReducedHomotopic

variable {H}



end ReducedHomotopic



namespace HeteroReducedHomotopic

variable {H}









end HeteroReducedHomotopic











noncomputable section

variable [Fintype V] (s : V → V) (hs : ∀ v, H.Adj v (s v))



set_option backward.isDefEq.respectTransparency false in
theorem doubleEdgePath_sheet_swap {a b : V} (h : H.Adj a b) (σ : Bool)
    (t : unitInterval) :
    SupportPair.swap H (doubleEdgePath H s hs (liftedEdge H h σ) t) =
      doubleEdgePath H s hs (liftedEdge H h (!σ)) t := by
  cases σ
  · exact congrArg (fun P => P t)
      (SupportPair.doubleEdgePath_map_swap H (hs a) h (hs b).symm)
  · have he := congrArg Path.symm
      (SupportPair.doubleEdgePath_map_swap H (hs b) h.symm (hs a).symm)
    simp only [Path.map_symm, Path.symm_symm] at he
    exact congrArg (fun P => P t) he



end

end AbelianTargets

end

/-!
# Binary lifts of graph walks

Walks lift to the bipartite double cover with the sheet determined by their
length parity.  This is the combinatorial covering step in Lemma 6.2.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
variable {V : Type*} (H : SimpleGraph V)
variable [Fintype V] (s : V → V) (hs : ∀ v, H.Adj v (s v))

set_option backward.isDefEq.respectTransparency false

theorem solution {a b : V} (p : H.Walk a b) (σ : Bool) (t : unitInterval) :
    SupportPair.swap H (supportLiftPath H s hs p σ t) = supportLiftPath H s hs p (!σ) t := by
  induction p generalizing σ t with
  | nil => cases σ <;> rfl
  | @cons a b c h p ih =>
    change SupportPair.swap H
      (((doubleEdgePath H s hs (liftedEdge H h σ)).trans (supportLiftPath H s hs p (!σ))) t) =
      ((doubleEdgePath H s hs (liftedEdge H h (!σ))).trans
        (supportLiftPath H s hs p (!(!σ)))) t
    simp only [Path.trans_apply]
    split_ifs
    · exact doubleEdgePath_sheet_swap H s hs h σ _
    · exact ih (!σ) _
