-- Prove2me | Definitions.Def_AT260939824_AtlasBoundaryTransverseBounds
-- name    : AT260939824_AtlasBoundaryTransverseBounds
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:03:13.517068+00:00
-- url     : https://prove2.me/theorems/3370870f-69c1-4a71-af40-911da760bb53
-- title:
--   Transverse boundary rates on an atlas prism
-- statement:
--   Let $C_j$ be coordinate bounds for compatible lower-cell maps on a cell $R$, and let $w_j$ denote its side widths. Only positive-width transverse coordinates are retained in the normalized prism boundary. A common transverse rate is
--
--   $$ B_R=2\sum_{j\text{ active},\,j\ne i} C_jw_j/2+1. $$
--
--   The accompanying face and boundary estimates make this rate applicable to each fixed longitudinal parameter, including cells with collapsed coordinates.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/AtlasBoundaryTransverseBounds.lean, selected declaration lines 13-18, 24-120, 122-123, 125-143; SHA-256 bf57610756c8671371d2bfda6b70e35d5c1ae15e4f9e61b7090063745d1552f1. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoundaryCoordinateBounds
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_CubeFaceCoordinateBounds
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntegerGridIntervals
import Definitions.Def_AT260939824_IntegerPrismChart
import Definitions.Def_AT260939824_IntegerPrismFilling
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_OrbitMarkerCuts
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_PriorityCuts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_RectangularAtlasBoundary
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RectangularCone
import Definitions.Def_AT260939824_RectangularTranslation
import Definitions.Def_AT260939824_RegularAnisotropicAtlas
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyConstant.Basic
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

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace AbelianTargets
noncomputable section
open scoped NNReal unitInterval BigOperators
variable {d : ℕ}

theorem prismBoundaryPoint_active (R : RectangularCell d) (i : Fin d)
    (v : ConeSphere (R.ActiveTransverse i→ℝ)) (r : I) (j : R.ActiveTransverse i) :
    (prismBoundaryPoint R i v r).val j.val=
      ((R.lower j.val : ℝ)+(R.upper j.val : ℝ))/2+R.transverseWidth j.val/2*v.val j := by
  simp only [prismBoundaryPoint,RectangularCell.prismPoint,RectangularCell.prismCoordinates,
    dif_neg j.property.1,dif_pos j.property.2]

namespace LowerCellCarrierMaps
variable {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d} {R : RectangularCell d}

theorem prism_transverse_coordinate_face (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (C : Fin d→ℝ≥0)
    (hcoord : ∀ (k : Fin d) (Q : RectangularCell d) (hQ : Q∈T.cells) (hrQ : Q.rank<R.rank)
      (z : RealCoordinates d) (x y : ℝ)
      (hx : Function.update z k x∈Q.closedBox) (hy : Function.update z k y∈Q.closedBox),
      dist (F.map Q hQ hrQ ⟨Function.update z k x,hx⟩)
        (F.map Q hQ hrQ ⟨Function.update z k y,hy⟩)≤C k*|x-y|)
    (r : I) (e a : R.ActiveTransverse i) (v w : ConeSphere (R.ActiveTransverse i→ℝ))
    (hext : |v.val e|=1) (hface : v.val e=w.val e)
    (heq : ∀ b,b≠a → v.val b=w.val b) :
    dist (F.boundaryValue hR (prismBoundaryPoint R i v r))
      (F.boundaryValue hR (prismBoundaryPoint R i w r))≤
      (C a.val : ℝ)*(R.transverseWidth a.val/2)*|v.val a-w.val a| := by
  classical
  have hwa := R.transverseWidth_pos i a
  by_cases hae : a=e
  · have hvw : v=w := by
      apply Subtype.ext
      funext b
      by_cases hba : b=a
      · subst b; simpa [hae] using hface
      · exact heq b hba
    rw [hvw,dist_self]
    positivity
  let z := (prismBoundaryPoint R i v r).val
  let z' := (prismBoundaryPoint R i w r).val
  have hzz : ∀ k,k≠a.val → z k=z' k := by
    intro k hka
    by_cases hki : k=i
    · subst k
      simp only [z,z',prismBoundaryPoint,RectangularCell.prismPoint_first]
    · by_cases hpos : R.lower k<R.upper k
      · let b : R.ActiveTransverse i := ⟨k,hki,hpos⟩
        have hba : b≠a := fun h => hka (congrArg Subtype.val h)
        have hh := heq b hba
        simpa only [z,z',prismBoundaryPoint,RectangularCell.prismPoint,
          RectangularCell.prismCoordinates,dif_neg hki,dif_pos hpos,b] using
          congrArg (fun u : ℝ => ((R.lower k : ℝ)+(R.upper k : ℝ))/2+R.transverseWidth k/2*u) hh
      · simp only [z,z',prismBoundaryPoint,RectangularCell.prismPoint,
          RectangularCell.prismCoordinates,dif_neg hki,dif_neg hpos]
  have hextcoord : z e.val=(R.lower e.val : ℝ) ∨ z e.val=(R.upper e.val : ℝ) := by
    have hv := abs_eq_abs.mp (show |v.val e|=|1| by simpa using hext)
    rcases hv with hv | hv
    · right
      dsimp only [z]
      rw [prismBoundaryPoint_active,hv]
      dsimp [RectangularCell.transverseWidth]
      ring
    · left
      dsimp only [z]
      rw [prismBoundaryPoint_active,hv]
      dsimp [RectangularCell.transverseWidth]
      ring
  have hev : e.val≠a.val := by
    intro h
    exact hae (Subtype.ext h.symm)
  have hline : ∀ s∈Set.Icc (R.lower a.val : ℝ) (R.upper a.val : ℝ),
      Function.update z a.val s∈R.boundary := by
    intro s hs
    refine ⟨?_,?_⟩
    · intro k
      by_cases hka : k=a.val
      · subst k; simpa using hs
      · simpa only [Function.update_of_ne hka] using (prismBoundaryPoint R i v r).property.1 k
    · intro hrel
      have hh := hrel e.val
      simp only [RectangularCell.relativeInterior,ne_of_lt e.property.2,if_false,
        Function.update_of_ne hev] at hh
      rcases hextcoord with h | h
      · rw [h] at hh
        exact (lt_irrefl _ hh.1)
      · rw [h] at hh
        exact (lt_irrefl _ hh.2)
  have hx := (prismBoundaryPoint R i v r).property.1 a.val
  have hy := (prismBoundaryPoint R i w r).property.1 a.val
  have hp : prismBoundaryPoint R i v r=⟨Function.update z a.val (z a.val),hline _ hx⟩ := by
    apply Subtype.ext
    funext k
    by_cases hk : k=a.val <;> simp [Function.update_of_ne,hk,z]
  have hq : prismBoundaryPoint R i w r=⟨Function.update z a.val (z' a.val),hline _ hy⟩ := by
    apply Subtype.ext
    funext k
    by_cases hk : k=a.val
    · subst k; simp [z']
    · simpa only [Function.update_of_ne hk] using (hzz k hk).symm
  have hh := F.boundary_coordinate_dist_le hR a.val (C a.val) (hcoord a.val)
    z hline (z a.val) (z' a.val) hx hy
  rw [←hp,←hq] at hh
  have hd : |z a.val-z' a.val|=R.transverseWidth a.val/2*|v.val a-w.val a| := by
    dsimp only [z,z']
    rw [prismBoundaryPoint_active,prismBoundaryPoint_active]
    have he : ((R.lower a.val : ℝ)+(R.upper a.val : ℝ))/2+R.transverseWidth a.val/2*v.val a-
        (((R.lower a.val : ℝ)+(R.upper a.val : ℝ))/2+R.transverseWidth a.val/2*w.val a)=
        (R.transverseWidth a.val/2)*(v.val a-w.val a) := by ring
    rw [he,abs_mul,abs_of_pos (by positivity : 0<R.transverseWidth a.val/2)]
  rw [hd] at hh
  simpa only [mul_assoc] using hh

def prismTransverseBound (R : RectangularCell d) (i : Fin d) (C : Fin d→ℝ≥0) : ℝ≥0 :=
  2*(∑ j : R.ActiveTransverse i,C j.val*(R.transverseWidth j.val).toNNReal/2)+1

theorem prism_transverse_lipschitz (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (C : Fin d→ℝ≥0)
    (hcoord : ∀ (k : Fin d) (Q : RectangularCell d) (hQ : Q∈T.cells) (hrQ : Q.rank<R.rank)
      (z : RealCoordinates d) (x y : ℝ)
      (hx : Function.update z k x∈Q.closedBox) (hy : Function.update z k y∈Q.closedBox),
      dist (F.map Q hQ hrQ ⟨Function.update z k x,hx⟩)
        (F.map Q hQ hrQ ⟨Function.update z k y,hy⟩)≤C k*|x-y|)
    (r : I) : LipschitzWith (prismTransverseBound R i C)
      (fun v : ConeSphere (R.ActiveTransverse i→ℝ) =>
        F.boundaryValue hR (prismBoundaryPoint R i v r)) := by
  apply lipschitz_cubeBoundary_of_coordinate_faces _
    (fun j : R.ActiveTransverse i => C j.val*(R.transverseWidth j.val).toNNReal/2) 1
  · intro v w
    exact Probability.dist_le_one _ _
  · intro e a v w hext hface heq
    have hh := F.prism_transverse_coordinate_face hR C hcoord r e a v w hext hface heq
    have hw := (R.transverseWidth_pos i a).le
    simpa only [NNReal.coe_div,NNReal.coe_mul,NNReal.coe_ofNat,Real.coe_toNNReal _ hw,
      mul_div_assoc,mul_assoc] using hh

end LowerCellCarrierMaps
end
end AbelianTargets


