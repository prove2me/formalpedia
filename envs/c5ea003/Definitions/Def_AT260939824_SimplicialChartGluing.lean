-- Prove2me | Definitions.Def_AT260939824_SimplicialChartGluing
-- name    : AT260939824_SimplicialChartGluing
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:20:26.203295+00:00
-- url     : https://prove2.me/theorems/5d25c61d-6304-4237-827d-3cf0c3b8e350
-- title:
--   Compatible charts on finite probability faces
-- statement:
--   For a finite vertex set $V$ and $s\subseteq V$, the probability face $\Delta_s$ consists of probability distributions whose positive support is contained in $s$. Given a finite family $F$ of such faces and a topological target $Z$, simplicial chart data assign a continuous map $\Delta_s\to Z$ to each $s\in F$.
--
--   The compatibility condition requires equal values whenever one distribution is supported on two chosen faces. Evaluation on the union of these faces selects any containing face and applies its chart. The agreement field is the mathematical condition that makes this selection independent of the face representation.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization; its implementation definitions are not asserted to be separately numbered in the paper. Original Lean module AbelianTargets/SimplicialChartGluing.lean, selected declaration lines 17-18, 20-26, 32-34, 36-39; SHA-256 90bbfc709b2c54d9957a7441f8595b904d0683b34c0c20caf806e8ae237cca7c. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplexMetricGluing
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
import Mathlib.Topology.LocallyFinite
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

/-!
# Concrete continuous maps from finite probability-simplex carriers

Continuous face charts agreeing on their literal intersections produce an
actual global continuous map. The construction chooses a supporting face,
and the agreement proof makes its value independent of that choice.
-/

namespace AbelianTargets

noncomputable section

abbrev ProbabilityFace {V : Type*} [Fintype V] (s : Finset V) :=
  {p : Probability V // p.SupportedOn (s : Set V)}

structure SimplicialChartData {V : Type*} [Fintype V] (F : Finset (Finset V))
    (Z : Type*) [TopologicalSpace Z] where
  chart : ∀ s, s ∈ F → ProbabilityFace s → Z
  continuous_chart : ∀ s hs, Continuous (chart s hs)
  agree : ∀ (s : Finset V) (hs : s ∈ F) (t : Finset V) (ht : t ∈ F)
    (p : Probability V) (hps : p.SupportedOn (s : Set V))
    (hpt : p.SupportedOn (t : Set V)), chart s hs ⟨p,hps⟩=chart t ht ⟨p,hpt⟩

namespace SimplicialChartData

variable {V Z : Type*} [Fintype V] [TopologicalSpace Z] {F : Finset (Finset V)}

def eval (D : SimplicialChartData F Z) (p : SimplicialCarrier F) : Z :=
  D.chart (Classical.choose p.2) (Classical.choose_spec p.2).1
    ⟨p.1,(Classical.choose_spec p.2).2⟩

theorem eval_eq_chart (D : SimplicialChartData F Z) (p : SimplicialCarrier F)
    (s : Finset V) (hs : s ∈ F) (hp : p.1.SupportedOn (s : Set V)) :
    D.eval p=D.chart s hs ⟨p.1,hp⟩ :=
  D.agree _ _ s hs p.1 _ hp









end SimplicialChartData

end

end AbelianTargets


