-- Prove2me | Definitions.Def_AT260939824_SimplexMetricGluing
-- name    : AT260939824_SimplexMetricGluing
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:04:01.099848+00:00
-- url     : https://prove2.me/theorems/ca4685e2-c657-40e2-9c7f-0b031425403e
-- title:
--   Common probability points and finite unions of simplex faces
-- statement:
--   For probability masses $\mu,\nu$ on a finite set $V$, define their overlap mass by
--   $$\omega(\mu,\nu)=\sum_{v\in V}\min\{\mu(v),\nu(v)\}.$$
--   When $\omega(\mu,\nu)>0$, their normalized common point is the probability mass
--   $$c(\mu,\nu)(v)=\frac{\min\{\mu(v),\nu(v)\}}{\omega(\mu,\nu)}.$$
--   For a finite family $\mathcal F$ of finite vertex sets, its simplicial carrier is the literal union of the corresponding probability-simplex faces: those $\mu$ whose positive support is contained in some $s\in\mathcal F$. These definitions support metric gluing across overlapping faces.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/SimplexMetricGluing.lean, selected declaration lines 23, 53-59, 122-124; SHA-256 a112f1f9eb0c83d8e4e0ea92718dc13a5f627288134b94aa28b4e924dd5a3608. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Init
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
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

/-!
# A common-face estimate for finite probability simplices

Two nearby probability points have a normalized coordinatewise minimum
supported in both of their support sets. This quantitative fact permits
Lipschitz estimates on simplex charts to be glued without an intrinsic-metric
assumption. The image diameter handles pairs with disjoint supports.
-/

namespace AbelianTargets

open scoped BigOperators NNReal

noncomputable section

namespace Probability

variable {V : Type*} [Fintype V]

def overlapMass (p q : Probability V) : ℝ := ∑ v, min (p.mass v) (q.mass v)









def commonPoint (p q : Probability V) (h : 0 < overlapMass p q) : Probability V where
  mass v := min (p.mass v) (q.mass v) / overlapMass p q
  nonneg v := div_nonneg (le_min (p.nonneg v) (q.nonneg v)) h.le
  sum_one := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    exact mul_inv_cancel₀ (ne_of_gt h)









end Probability

/-- The literal union of a finite collection of probability-simplex faces. -/
abbrev SimplicialCarrier {V : Type*} [Fintype V] (F : Finset (Finset V)) :=
  {p : Probability V // ∃ s ∈ F, p.SupportedOn (s : Set V)}



end

end AbelianTargets


