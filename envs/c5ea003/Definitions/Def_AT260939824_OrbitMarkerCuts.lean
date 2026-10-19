-- Prove2me | Definitions.Def_AT260939824_OrbitMarkerCuts
-- name    : AT260939824_OrbitMarkerCuts
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:45:47.30253+00:00
-- url     : https://prove2.me/theorems/c10dcbdb-df24-492a-bf64-5f4c53aa8364
-- title:
--   Pullback of a finite priority neighborhood along an injection
-- statement:
--   Let $I,J$ be sets, $P\in\mathbb N$, and let priority-neighborhood data on $J$ consist of finite sets $N(j)$ of size at most $P$, a symmetric neighborhood relation, and priorities $c:J\to\{0,\ldots,P-1\}$ that differ on distinct neighboring points. For an injection $f:I\to J$, define the pulled-back data by
--   $$N_f(i)=\{i'\in I:f(i')\in N(f(i))\},\qquad c_f(i)=c(f(i)).$$
--   Injectivity keeps these neighborhoods finite with the same bound and preserves proper priorities. In particular,
--   $$i'\in N_f(i)\ \Longleftrightarrow\ f(i')\in N(f(i)).$$
--   This construction transports priority data from actual marker points to their orbit-coordinate representatives.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/OrbitMarkerCuts.lean, selected declaration lines 19-32, 34-37; SHA-256 15b5ac16218d676a2e706c583622e6436cfa9615a1fd600c80583c30214e6c21. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_PriorityCuts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-!
# Priority cuts in actual orbit coordinates

A free action identifies each orbit marker with its lattice coordinate.
Pulling the actual finite marker neighborhood back along this injection
gives the priority input on that orbit. Coordinatewise iteration then
constructs literal `RectangularCuts`, including the side bounds and
separation of cuts of nearby markers. The retained-box CW subdivision
is a separate construction.
-/

namespace AbelianTargets
noncomputable section

def PriorityNeighborhood.pullback {I J : Type*} {P : ℕ}
    (N : PriorityNeighborhood J P) (f : I → J) (hf : Function.Injective f) :
    PriorityNeighborhood I P where
  nearby i := (N.nearby (f i)).preimage f hf.injOn
  bound i := by
    classical
    rw [Finset.card_preimage]
    exact (Finset.card_filter_le _ _).trans (N.bound (f i))
  symmetric i j hij := by
    apply Finset.mem_preimage.mpr
    exact N.symmetric _ _ (Finset.mem_preimage.mp hij)
  priority i := N.priority (f i)
  proper i j hij hne := N.proper _ _ (Finset.mem_preimage.mp hij)
    (fun h => hne (hf h))

@[simp] theorem PriorityNeighborhood.mem_pullback {I J : Type*} {P : ℕ}
    (N : PriorityNeighborhood J P) (f : I → J) (hf : Function.Injective f) (i j : I) :
    j ∈ (N.pullback f hf).nearby i ↔ f j ∈ N.nearby (f i) :=
  Finset.mem_preimage (hf := hf.injOn)

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X]



















end
end AbelianTargets


