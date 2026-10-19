-- Prove2me | Definitions.Def_AT260939824_ProbabilityTwoVertices
-- name    : AT260939824_ProbabilityTwoVertices
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:58:53.649757+00:00
-- url     : https://prove2.me/theorems/f197c6c7-aec0-4ad5-b1cb-1d3839bb39e7
-- title:
--   Barycentric formulas for one- and two-vertex probability masses
-- statement:
--   For a finite set $V$, a probability mass $\mu$ supported on a singleton $\{v\}$ equals $\delta_v$. If $v\ne w$ and $\mu$ is supported on $\{v,w\}$, then
--   $$\mu(v)+\mu(w)=1,\qquad \mu=(1-\mu(w))\delta_v+\mu(w)\delta_w.$$
--   For any coordinate function $c:V\to\mathbb R$, define the weighted coordinate and its finite bound by
--   $$x_c(\mu)=\sum_u\mu(u)c(u),\qquad C_c=\sum_u|c(u)|.$$
--   On a two-vertex support, $x_c(\mu)=\mu(v)c(v)+\mu(w)c(w)$. These formulas recover interval parameters from mass coordinates.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/ProbabilityTwoVertices.lean, selected declaration lines 11, 13-14, 32-40, 42-56, 58-73, 75-84; SHA-256 b519bc40567569c7d4afc3111657083941f20b383c0e75e0590b1a9d4542eaf9. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

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

/-! Exact barycentric coordinates on an edge, used to invert the literal
height-zero carrier parametrization. -/

namespace AbelianTargets.Probability
noncomputable section
open scoped BigOperators unitInterval NNReal
variable {V : Type*} [Fintype V]

def weightedCoordinate (c : V → ℝ) (p : Probability V) : ℝ := ∑ u,p.mass u*c u

def weightedCoordinateConstant (c : V → ℝ) : ℝ≥0 :=
  ⟨∑ u,|c u|,Finset.sum_nonneg (fun u _ => abs_nonneg _)⟩



theorem mass_pair_sum (p : Probability V) (v w : V) (hne : v ≠ w)
    (hp : p.SupportedOn ({v,w} : Set V)) : p.mass v+p.mass w=1 := by
  classical
  have hsum : ∑ u ∈ ({v,w} : Finset V),p.mass u = ∑ u,p.mass u := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u hu hn
    apply (supportedOn_iff_zero.mp hp) u
    simpa using hn
  simpa [hne] using hsum.trans p.sum_one

theorem eq_mix_dirac_of_pair (p : Probability V) (v w : V) (hne : v ≠ w)
    (hp : p.SupportedOn ({v,w} : Set V)) :
    p = mix (dirac v) (dirac w) ⟨p.mass w,p.nonneg w,p.mass_le_one w⟩ := by
  classical
  have hs := p.mass_pair_sum v w hne hp
  ext u
  by_cases huv : u=v
  · subst u
    simp [mix_mass,dirac_mass,hne]
    linarith
  · by_cases huw : u=w
    · subst u
      simp [mix_mass,dirac_mass,hne.symm]
    · have hz : p.mass u=0 := (supportedOn_iff_zero.mp hp) u (by simp [huv,huw])
      simp [mix_mass,dirac_mass,huv,huw,hz]

theorem eq_dirac_of_singleton (p : Probability V) (v : V)
    (hp : p.SupportedOn ({v} : Set V)) : p=dirac v := by
  classical
  have hs : p.mass v=1 := by
    have hsum : ∑ u ∈ ({v} : Finset V),p.mass u = ∑ u,p.mass u := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro u hu hn
      apply (supportedOn_iff_zero.mp hp) u
      simpa using hn
    simpa using hsum.trans p.sum_one
  ext u
  by_cases hu : u=v
  · subst u
    simp [dirac_mass,hs]
  · have hz := (supportedOn_iff_zero.mp hp) u (by simp [hu])
    simp [dirac_mass,hu,hz]

theorem weighted_pair_sum (p : Probability V) (v w : V) (hne : v ≠ w)
    (hp : p.SupportedOn ({v,w} : Set V)) (c : V → ℝ) :
    ∑ u,p.mass u*c u=p.mass v*c v+p.mass w*c w := by
  classical
  have hsum : ∑ u ∈ ({v,w} : Finset V),p.mass u*c u = ∑ u,p.mass u*c u := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u hu hn
    have hz := (supportedOn_iff_zero.mp hp) u (by simpa using hn)
    simp [hz]
  simpa [hne] using hsum.symm





end
end AbelianTargets.Probability


