-- Prove2me | Definitions.Def_AT260939824_CarrierCharts
-- name    : AT260939824_CarrierCharts
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:58:15.728595+00:00
-- url     : https://prove2.me/theorems/776d0762-0b88-426a-b877-66dafc613446
-- title:
--   Affine simplex charts for carrier probabilities
-- statement:
--   For a finite vertex set $V$ and finite subset $s$, its probability face chart is
--
--   $$ \Delta_s=\{f:V\to\mathbb R: f\ge0,\ \sum_vf(v)=1,\ f(v)=0\text{ for }v\notin s\}. $$
--
--   These charts are convex. The carrier realization embeds isometrically into its ambient mass-coordinate space, and each permitted face chart lies in that ambient realization. This provides the affine charts used for geometric row interpolation.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CarrierCharts.lean, selected declaration lines 12-13, 15-26, 28-30, 32-34, 39-40, 42-47, 49-55; SHA-256 0c60dcd1b3e37028ed5f5f7d1aedac6895a76e5457be73afa16cacae6b47293a. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
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

/-! Convex ambient charts of the actual finite interval carrier. -/

namespace AbelianTargets
open scoped BigOperators
noncomputable section
namespace Probability

variable {V : Type*} [Fintype V]

def faceChart (s : Finset V) : Set (V → ℝ) :=
  {f | (∀ v, 0 ≤ f v) ∧ (∑ v, f v = 1) ∧ ∀ v ∉ s, f v = 0}

theorem faceChart_convex (s : Finset V) : Convex ℝ (faceChart s) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_,?_,?_⟩
  · intro v
    exact add_nonneg (mul_nonneg ha (hx.1 v)) (mul_nonneg hb (hy.1 v))
  · change ∑ v, (a*x v+b*y v) = 1
    rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hx.2.1,hy.2.1]
    simpa only [mul_one] using hab
  · intro v hv
    change a*x v+b*y v = 0
    rw [hx.2.2 v hv,hy.2.2 v hv]
    simp

theorem mass_mem_faceChart (p : Probability V) (s : Finset V)
    (hp : p.SupportedOn (s : Set V)) : p.mass ∈ faceChart s :=
  ⟨p.nonneg,p.sum_one,fun v hv => supportedOn_iff_zero.mp hp v hv⟩

theorem dirac_mem_faceChart (s : Finset V) (v : V) (hv : v ∈ s) :
    (dirac v).mass ∈ faceChart s :=
  mass_mem_faceChart _ _ (supportedOn_dirac v hv)

end Probability
namespace IntervalCarriers

def ambientRealization (m K : ℕ) (A B : ℤ) : Set (CarrierVertex K A B → ℝ) :=
  Set.range (fun p : Realization m K A B => p.1.mass)

def ambientEquiv (m K : ℕ) (A B : ℤ) :
    Realization m K A B ≃ᵢ {f : CarrierVertex K A B → ℝ // f ∈ ambientRealization m K A B} where
  toEquiv := Equiv.ofInjective (fun p : Realization m K A B => p.1.mass) (by
    intro p q h
    exact Subtype.ext (Probability.ext h))
  isometry_toFun := by intro p q; rfl

theorem faceChart_subset_ambient {m K : ℕ} {A B : ℤ} (s : Finset (CarrierVertex K A B))
    (hs : CarrierFace m K A B (s.image Subtype.val)) :
    Probability.faceChart s ⊆ ambientRealization m K A B := by
  intro f hf
  let p : Probability (CarrierVertex K A B) := ⟨f,hf.1,hf.2.1⟩
  have hp : p.SupportedOn (s : Set _) := Probability.supportedOn_iff_zero.mpr hf.2.2
  exact ⟨⟨p,s,(mem_simplexFaces s).mpr hs,hp⟩,rfl⟩

end IntervalCarriers
end
end AbelianTargets


