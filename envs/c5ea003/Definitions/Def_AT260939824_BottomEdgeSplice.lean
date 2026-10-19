-- Prove2me | Definitions.Def_AT260939824_BottomEdgeSplice
-- name    : AT260939824_BottomEdgeSplice
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:56:38.844054+00:00
-- url     : https://prove2.me/theorems/ecc10199-4827-494b-b7a8-9a9762f32142
-- title:
--   Controlled splice records for moving bottom endpoints
-- statement:
--   In a normed real space $E$, a splice record contains a based vertex row ending at $p$, a carry homotopy between rows ending at $q$, and a target subset $S$. Its hypotheses record edge bounds $\Delta$, convex face charts, correspondence bounds, and finite joint Lipschitz control. Its associated family satisfies
--
--   $$F(r,0)=\mathrm{base},\qquad F(r,1)=(1-r)p+rq.$$
--
--   At $r=0$ and $r=1$ it agrees with the prescribed initial and appended target rows. These endpoint and side identities supply the interface for joining successive pieces of the bottom combing.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/BottomEdgeSplice.lean, selected declaration lines 11-13, 23-26, 28-29, 31-52, 58-61, 103-109, 111-119, 121-142, 144-145, 147-155; SHA-256 52ee5fad572bee063a7c8d5d7961cbf69683a2cd2a80d8a9a1c13678b8c3a44f. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_RowSlotScaling
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_WordPathHelpers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/-! The complete moving-endpoint family across one bottom edge. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def halfPoint : unitInterval := ⟨1/2,by constructor <;> norm_num⟩
def upperHalf (r : unitInterval) : unitInterval :=
  ⟨((r : ℝ)+1)/2,by constructor <;> linarith [r.property.1,r.property.2]⟩



theorem interval_dist_le_one (r s : unitInterval) : dist r s ≤ 1 := by
  change |(r : ℝ)-(s : ℝ)| ≤ 1
  rw [abs_le]
  constructor <;> linarith [r.property.1,r.property.2,s.property.1,s.property.2]

theorem mix_eq_lineMap (a b : E) (r : unitInterval) :
    mix a b r = AffineMap.lineMap a b (r : ℝ) := (AffineMap.lineMap_apply_module _ _ _).symm

structure BottomSpliceData (n : ℕ) (base p q : E) (S : Set E) (Δ : ℝ≥0) where
  leftRow : ℕ → E
  carrySource : BasedRow n base q
  carryTarget : BasedRow n base q
  left_source : leftRow 0 = base
  left_target : leftRow (n+2) = p
  left_edges : ∀ j ≤ n+1, dist (leftRow j) (leftRow (j+1)) ≤ Δ
  seam_edges : ∀ j ≤ n+1,
    dist (appendRowEndpoint carrySource.vertices n (mix p q halfPoint) j)
      (appendRowEndpoint carrySource.vertices n (mix p q halfPoint) (j+1)) ≤ Δ
  left_charts : ∀ j ≤ n+1, ∃ F : Set E, Convex ℝ F ∧ F ⊆ S ∧
    leftRow j ∈ F ∧ leftRow (j+1) ∈ F ∧
    appendRowEndpoint carrySource.vertices n (mix p q halfPoint) j ∈ F ∧
    appendRowEndpoint carrySource.vertices n (mix p q halfPoint) (j+1) ∈ F
  corresponding_bound : ∃ C : ℝ≥0, ∀ j ≤ n+2,
    dist (leftRow j) (appendRowEndpoint carrySource.vertices n (mix p q halfPoint) j) ≤ C
  edge_bound : dist p q ≤ Δ
  edge_chart : ∃ F : Set E, Convex ℝ F ∧ F ⊆ S ∧ p ∈ F ∧ q ∈ F
  carry : carrySource.path.Homotopy carryTarget.path
  carry_mem : ∀ t, carry t ∈ S
  carry_speed : ∀ r, LipschitzWith (Δ*(n+1)) (carry.eval r)
  carry_joint : ∃ J : ℝ≥0, LipschitzWith J carry

namespace BottomSpliceData
variable {n : ℕ} {base p q : E} {S : Set E} {Δ : ℝ≥0}
variable (D : BottomSpliceData n base p q S Δ)

def seamRow : ℕ → E := appendRowEndpoint D.carrySource.vertices n (mix p q halfPoint)
def leftFamily := rowFamily D.leftRow D.seamRow (n+1)
def rightFamily := correctedCarry n D.carry q (fun r => mix p q (upperHalf r))
def family := halfGlue D.leftFamily D.rightFamily









theorem family_mem (t : unitInterval × unitInterval) : D.family t ∈ S := by
  apply halfGlue_mem _ _ _ _ t
  · exact rowFamily_mem_charts D.leftRow D.seamRow (n+1) D.left_charts
  · apply correctedCarry_mem n D.carry q _ D.carry_mem
    intro r t
    obtain ⟨F,hconv,hsub,hp,hq⟩ := D.edge_chart
    exact hsub (mix_mem hconv hq (mix_mem hconv hp hq (upperHalf r)) t)

@[simp] theorem family_source (r : unitInterval) : D.family (r,0) = base := by
  unfold family halfGlue halfGlueRaw leftFamily rightFamily
  split_ifs
  · rw [rowFamily_source,D.left_source]
    have hs : D.seamRow 0 = base := by
      simp only [seamRow,appendRowEndpoint,if_pos (show 0 ≤ n+1 by omega),D.carrySource.source]
    rw [hs,mix_self]
  · rw [correctedCarry_source]
    exact D.carry.source _

@[simp] theorem family_target (r : unitInterval) : D.family (r,1) = mix p q r := by
  unfold family halfGlue halfGlueRaw leftFamily rightFamily
  split_ifs with hr
  · rw [rowFamily_target,D.left_target]
    have ht : D.seamRow (n+1+1) = mix p q halfPoint := by
      simp only [seamRow,appendRowEndpoint,if_neg (show ¬n+1+1 ≤ n+1 by omega)]
    rw [ht]
    have htime : 0 ≤ 2*(r : ℝ) ∧ 2*(r : ℝ) ≤ 1 := by constructor <;> linarith [r.property.1]
    rw [show clampInterval (2*(r : ℝ)) = ⟨_,htime⟩ from clampInterval_coe ⟨_,htime⟩]
    rw [mix_eq_lineMap,mix_eq_lineMap,mix_eq_lineMap]
    change AffineMap.lineMap p (AffineMap.lineMap p q (1/2 : ℝ)) (2*(r : ℝ)) = _
    rw [AffineMap.lineMap_lineMap_right]
    congr 1
    ring
  · rw [correctedCarry_target]
    have htime : 0 ≤ 2*(r : ℝ)-1 ∧ 2*(r : ℝ)-1 ≤ 1 := by
      constructor <;> linarith [r.property.2]
    rw [show clampInterval (2*(r : ℝ)-1) = ⟨_,htime⟩ from clampInterval_coe ⟨_,htime⟩]
    congr 1
    apply Subtype.ext
    change ((2*(r : ℝ)-1)+1)/2 = (r : ℝ)
    ring

@[simp] theorem family_zero (u : unitInterval) : D.family (0,u) = asPath D.leftRow (n+1) u := by
  rw [family,halfGlue_zero,leftFamily,rowFamily_zero]

@[simp] theorem family_one (u : unitInterval) : D.family (1,u) =
    asPath (appendRowEndpoint D.carryTarget.vertices n q) (n+1) u := by
  rw [family,halfGlue_one]
  have hh := correctedCarry_row_eq n D.carryTarget.vertices q
    (fun r => mix p q (upperHalf r)) D.carry 1
    (fun u => D.carry.map_one_left u) D.carryTarget.target u
  have he : upperHalf 1 = 1 := by apply Subtype.ext; norm_num [upperHalf]
  rw [he,mix_one] at hh
  exact hh

end BottomSpliceData
end
end AbelianTargets.FixedSlots


