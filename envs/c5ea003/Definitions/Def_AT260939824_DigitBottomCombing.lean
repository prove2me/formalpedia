-- Prove2me | Definitions.Def_AT260939824_DigitBottomCombing
-- name    : AT260939824_DigitBottomCombing
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:17:55.866734+00:00
-- url     : https://prove2.me/theorems/4f2662f8-1714-4208-8510-82dbf0eb0254
-- title:
--   Digit combing of a finite bottom interval
-- statement:
--   Let $m\ge2$ be an integer base and $R$ a natural number. Compressed digit paths and consecutive endpoint splices define one common-slot combing along the bottom interval from $0$ to $R$. Its values are real probability coordinates on the finite carrier of height $\log_m R$. For $R>0$, the whole parametrized combing stays in the carrier realization.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/DigitBottomCombing.lean, selected declaration lines 9-10, 12-14, 20-23, 40-42, 44-47, 54-56, 85-90, 92-106, 108-126, 128-146; SHA-256 48e0c9a55650c0807638d1eb4fe9275002aa2a2da4a0e46760e1539ac3eb4b80. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_BottomIntervalMap
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierCharts
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitBottomData
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FiniteIntervalGluing
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_JointCarrierRows
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_WordPathHelpers
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
import Mathlib.Data.List.Chain
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

/-! The actual digit combing of the entire finite bottom interval, with common slots. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section

def digitSplice (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n < R) :=
  Classical.choose (exists_bottomSpliceData m hm R n hn)

theorem digitSplice_leftRow (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n < R) :
    (digitSplice m hm R n hn).leftRow = bottomRow m hm R n (by omega) :=
  (Classical.choose_spec (exists_bottomSpliceData m hm R n hn)).1



theorem digitSplice_zero (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n < R)
    (u : unitInterval) : (digitSplice m hm R n hn).family (0,u) =
    FixedSlots.asPath (bottomRow m hm R n (by omega)) (carryRowBudget m R+1) u := by
  rw [FixedSlots.BottomSpliceData.family_zero,digitSplice_leftRow]



def digitEdgeFamily (m : ℕ) (hm : 2 ≤ m) (R n : ℕ)
    (z : unitInterval × unitInterval) : CarrierVertex (Nat.log m R) 0 R → ℝ :=
  if hn : n < R then (digitSplice m hm R n hn).family z else bottomMass (Nat.log m R) R 0

theorem digitEdgeFamily_eq (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n < R) :
    digitEdgeFamily m hm R n = (digitSplice m hm R n hn).family := by
  funext z
  simp only [digitEdgeFamily,dif_pos hn]



def bottomCombing (m : ℕ) (hm : 2 ≤ m) (R : ℕ) :
    ℝ × unitInterval → (CarrierVertex (Nat.log m R) 0 R → ℝ) :=
  FixedSlots.intervalGlue (digitEdgeFamily m hm R) (R-1)







theorem bottomCombing_mem (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (z : ℝ × unitInterval) : bottomCombing m hm R z ∈ ambientRealization m (Nat.log m R) 0 R := by
  apply FixedSlots.intervalGlue_mem
  intro i hi z
  rw [digitEdgeFamily_eq m hm R i (by omega)]
  exact (digitSplice m hm R i (by omega)).family_mem z

@[simp] theorem bottomCombing_source (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (x : ℝ) : bottomCombing m hm R (x,0) = bottomMass (Nat.log m R) R 0 := by
  unfold bottomCombing
  have he := FixedSlots.intervalGlue_eval_eq (digitEdgeFamily m hm R)
    (fun _ _ => bottomMass (Nat.log m R) R 0) (R-1) 0 (fun i hi r => by
      rw [digitEdgeFamily_eq m hm R i (by omega)]
      exact (digitSplice m hm R i (by omega)).family_source r) x
  rw [he]
  have hc : ∀ n, FixedSlots.intervalGlue (fun _ _ => bottomMass (Nat.log m R) R 0) n (x,0) =
      bottomMass (Nat.log m R) R 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [FixedSlots.intervalGlue]; split <;> first | exact ih | rfl
  exact hc _

@[simp] theorem bottomCombing_target (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (x : ℝ) : bottomCombing m hm R (x,1) = bottomMap (Nat.log m R) R x := by
  unfold bottomCombing bottomMap
  have he := FixedSlots.intervalGlue_eval_eq (digitEdgeFamily m hm R)
    (fun i z => FixedSlots.mix (bottomMass (Nat.log m R) R i)
      (bottomMass (Nat.log m R) R (i+1)) z.1) (R-1) 1 (fun i hi r => by
      rw [digitEdgeFamily_eq m hm R i (by omega)]
      exact (digitSplice m hm R i (by omega)).family_target r) x
  rw [he]
  have hc : ∀ n, ∀ u v : unitInterval,
      FixedSlots.intervalGlue (fun i z => FixedSlots.mix (bottomMass (Nat.log m R) R i)
        (bottomMass (Nat.log m R) R (i+1)) z.1) n (x,u) =
      FixedSlots.intervalGlue (fun i z => FixedSlots.mix (bottomMass (Nat.log m R) R i)
        (bottomMass (Nat.log m R) R (i+1)) z.1) n (x,v) := by
    intro n u v
    induction n with
    | zero => rfl
    | succ n ih => simp only [FixedSlots.intervalGlue]; split <;> first | exact ih | rfl
  exact hc _ _ _

@[simp] theorem bottomCombing_base (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (u : unitInterval) : bottomCombing m hm R (0,u) = bottomMass (Nat.log m R) R 0 := by
  rw [bottomCombing,FixedSlots.intervalGlue_zero,digitEdgeFamily_eq m hm R 0 hR,digitSplice_zero]
  have hrow : bottomRow m hm R 0 (Nat.zero_le R) =
      fun _ => bottomMass (Nat.log m R) R 0 := by
    funext j
    apply bottomRow_terminal
    simp only [compressedWord_zero,List.length_nil]
    exact Nat.zero_le _
  rw [hrow]
  have hc : ∀ T k u, FixedSlots.rowPath T (fun _ => bottomMass (Nat.log m R) R 0) k u =
      bottomMass (Nat.log m R) R 0 := by
    intro T k u
    induction k with
    | zero => exact AffineMap.lineMap_same_apply _ _
    | succ k ih => simp only [FixedSlots.rowPath]; split <;> first
        | exact ih
        | exact AffineMap.lineMap_same_apply _ _
  exact hc _ _ _

end
end AbelianTargets.IntervalCarriers


