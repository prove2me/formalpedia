-- Prove2me | Definitions.Def_AT260939824_ProbabilityPushDirac
-- name    : AT260939824_ProbabilityPushDirac
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:50:55.510815+00:00
-- url     : https://prove2.me/theorems/3b3d7038-3ad0-4a83-abb4-d66f83540234
-- title:
--   Dirac masses under finite probability pushforward
-- statement:
--   For finite sets $V,W$, a map $f:V\to W$, and a vertex $v\in V$, pushforward of a probability mass $\mu$ is given by $(f_*\mu)(w)=\sum_{f(u)=w}\mu(u)$. The selected compatibility identity is
--   $$f_*\delta_v=\delta_{f(v)},$$
--   where $\delta_v$ assigns mass one to $v$ and zero elsewhere. It identifies the images of carrier vertices under coordinate inclusions and translations.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/ProbabilityPushDirac.lean, selected declaration lines 7-15; SHA-256 2c4b2d109840f78e0fb51b79684fad771e7724e6833a8e84c19b20d589a198ec. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CompressedWords
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

namespace AbelianTargets.Probability
noncomputable section
variable {V W : Type*} [Fintype V] [Fintype W]

@[simp] theorem push_dirac (f : V → W) (v : V) : push f (dirac v)=dirac (f v) := by
  classical
  ext w
  rw [push_mass]
  rw [Finset.sum_eq_single v]
  · simp [dirac_mass,eq_comm]
  · intro u hu huv
    simp [dirac_mass,huv]
  · simp

end
end AbelianTargets.Probability


