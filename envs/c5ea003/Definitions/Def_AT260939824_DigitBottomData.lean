-- Prove2me | Definitions.Def_AT260939824_DigitBottomData
-- name    : AT260939824_DigitBottomData
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:16:27.241901+00:00
-- url     : https://prove2.me/theorems/f236988a-4f6b-4107-ab1f-eb35f5111d44
-- title:
--   Compressed bottom paths and splice data
-- statement:
--   For an integer base $m\ge2$ and $0\le n\le R$, compressed words are realized as actual directed paths from $(0,0)$ to $(n,0)$. Their vertices remain in the finite carrier between $0$ and $R$ at logarithmic height. The bundle also constructs the one-edge step from $n$ to $n+1$, common-slot bottom rows, and the moving-endpoint splice data for consecutive rows.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/DigitBottomData.lean, selected declaration lines 10-13, 15-18, 20-21, 23-26, 28-35, 37-94; SHA-256 283d7751053b0bb046e2633abc408bceaf4f57f6d5dc4d4d843938d0a7b98425. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AppendedSpliceData
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_BottomIntervalMap
import Definitions.Def_AT260939824_CanonicalRows
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierCharts
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierRowRealization
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedCarrierWalks
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ContextualCarrierRows
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_FixedSlotPadding
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_JointCarrierRows
import Definitions.Def_AT260939824_PaddedRowCoordinates
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_RowValidity
import Definitions.Def_AT260939824_SafeDigitalCarries
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleRowMoves
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

/-! Actual compressed digit paths supply every moving-endpoint splice datum. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section

def bottomWordPath (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n ≤ R) :
    WordPath m (0,0) (compressedWord m hm n) ((n : ℤ),0) :=
  Classical.choose ((compressedWord_positive m hm n).mono
    (Nat.log_mono_right hn) |>.exists_carrier_path hn)

theorem bottomWordPath_mem (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n ≤ R) :
    ∀ v ∈ (bottomWordPath m hm R n hn).vertices, v ∈ carrierVertices (Nat.log m R) 0 R :=
  Classical.choose_spec ((compressedWord_positive m hm n).mono
    (Nat.log_mono_right hn) |>.exists_carrier_path hn)

def bottomAStep (m n : ℕ) : WordPath m ((n : ℤ),0) [BSLetter.a] (((n+1 : ℕ) : ℤ),0) :=
  .cons (by simp [LetterStep,HorizontalStep,Nat.cast_add]) (.nil _)

def bottomRow (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n ≤ R) :
    ℕ → (CarrierVertex (Nat.log m R) 0 R → ℝ) :=
  FixedSlots.listRow (vertexMass (carrierBase (Nat.log m R) R)) ((n : ℤ),0)
    (bottomWordPath m hm R n hn).vertices

theorem bottomRow_terminal (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n ≤ R)
    (j : ℕ) (hj : (compressedWord m hm n).length ≤ j) :
    bottomRow m hm R n hn j = bottomMass (Nat.log m R) R n := by
  unfold bottomRow FixedSlots.listRow
  rw [list_getD_terminal (bottomWordPath m hm R n hn).vertices_last j (by
    rw [WordPath.vertices_length]
    omega)]
  rfl

theorem exists_bottomSpliceData (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n < R) :
    ∃ D : FixedSlots.BottomSpliceData (carryRowBudget m R)
      (bottomMass (Nat.log m R) R 0) (bottomMass (Nat.log m R) R n)
      (bottomMass (Nat.log m R) R (n+1))
      (ambientRealization m (Nat.log m R) 0 R) 1,
      D.leftRow = bottomRow m hm R n (by omega) ∧
      D.carryTarget.vertices = bottomRow m hm R (n+1) (by omega) := by
  let B := carryRowBudget m R
  let ι := vertexMass (carrierBase (Nat.log m R) R)
  let pn := bottomWordPath m hm R n (show n ≤ R by omega)
  let q := bottomWordPath m hm R (n+1) (show n+1 ≤ R by omega)
  let p := pn.append (bottomAStep m n)
  obtain ⟨p₀,q₀,hp₀,hq₀,hrows⟩ := exists_bounded_carrier_carry_rows m hm R n hn
  have hpv : p₀.vertices = p.vertices := p₀.vertices_eq p
  have hqv : q₀.vertices = q.vertices := q₀.vertices_eq q
  rw [hpv,hqv] at hrows
  have hp : ∀ v ∈ p.vertices, v ∈ carrierVertices (Nat.log m R) 0 R := by
    simpa only [hpv] using hp₀
  have hq : ∀ v ∈ q.vertices, v ∈ carrierVertices (Nat.log m R) 0 R := by
    simpa only [hqv] using hq₀
  have hverts : p.vertices = pn.vertices++[(((n+1 : ℕ) : ℤ),0)] := by
    simp only [p,WordPath.vertices_append_tail,bottomAStep,WordPath.vertices,List.tail_cons]
  have hl := hrows.length_bounds
  let U := FixedSlots.canonicalRow ι B (0,0) (((n+1 : ℕ) : ℤ),0)
    (padRow (B+2) (((n+1 : ℕ) : ℤ),0) p.vertices) (padRow_head p.vertices_head _)
    (padRow_last p.vertices_last _) (padRow_length (hl.1.trans (by dsimp [B,carryRowBudget]; omega)))
  let T := FixedSlots.canonicalRow ι B (0,0) (((n+1 : ℕ) : ℤ),0)
    (padRow (B+2) (((n+1 : ℕ) : ℤ),0) q.vertices) (padRow_head q.vertices_head _)
    (padRow_last q.vertices_last _) (padRow_length (hl.2.trans (by dsimp [B,carryRowBudget]; omega)))
  obtain ⟨F,hFS,hFL,hFJ⟩ := FixedSlots.boundedTriangleRows_realize_joint ι
    (carrierFace_charts _) (C := 1) (fun a b => Probability.dist_le_one _ _) hrows
    (0,0) (((n+1 : ℕ) : ℤ),0) p.vertices_head p.vertices_last (p.validRow (by omega) hp)
  have hU : U.vertices = FixedSlots.listRow ι (((n+1 : ℕ) : ℤ),0)
      (pn.vertices++[(((n+1 : ℕ) : ℤ),0)]) := by
    funext j
    change ι ((padRow (B+2) (((n+1 : ℕ) : ℤ),0) p.vertices).getD j (((n+1 : ℕ) : ℤ),0)) = _
    rw [padRow_getD,hverts]
    rfl
  have hface : CarrierFace m (Nat.log m R) 0 R {((n : ℤ),0),(((n+1 : ℕ) : ℤ),0)} := by
    exact Or.inr (Or.inl ⟨_,(bottomVertex _ R n (by omega)).property,
      _,(bottomVertex _ R (n+1) (by omega)).property,
      (show LetterStep m BSLetter.a ((n : ℤ),0) (((n+1 : ℕ) : ℤ),0) from by
        simp [LetterStep,HorizontalStep,Nat.cast_add]).adj (by omega),Finset.Subset.refl _⟩)
  have hlen : pn.vertices.length ≤ B+1 := by
    rw [WordPath.vertices_length]
    have hh := compressedWord_interval_uniform_length m hm R n (show n ≤ R by omega)
    dsimp [B,carryRowBudget]
    omega
  let D := FixedSlots.appendedSpliceData ι (carrierFace_charts _) (C := 1)
    (fun a b => Probability.dist_le_one _ _) B (0,0) ((n : ℤ),0) (((n+1 : ℕ) : ℤ),0)
    pn.vertices pn.vertices_head pn.vertices_last (pn.validRow (by omega)
      (bottomWordPath_mem m hm R n (by omega))) hface hlen U T hU F hFS
    (by simpa only [one_mul] using hFL) hFJ
  refine ⟨D,rfl,?_⟩
  funext j
  change ι ((padRow (B+2) (((n+1 : ℕ) : ℤ),0) q.vertices).getD j (((n+1 : ℕ) : ℤ),0)) = _
  rw [padRow_getD]
  rfl

end
end AbelianTargets.IntervalCarriers


