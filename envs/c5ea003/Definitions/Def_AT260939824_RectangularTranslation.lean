-- Prove2me | Definitions.Def_AT260939824_RectangularTranslation
-- name    : AT260939824_RectangularTranslation
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:48:49.87897+00:00
-- url     : https://prove2.me/theorems/f54309c5-e8d1-467c-9590-0f3acc3db2c4
-- title:
--   Translation of coordinates, rectangles, and tilings
-- statement:
--   For $a\in\mathbb Z^d$ and $x\in\mathbb R^d$, define $T_a(x)_i=x_i+a_i$. Translate an integer rectangle by adding $a$ to both endpoints, and translate a tiling by translating each of its tiles. The defining compatibility laws are
--   $$T_aT_{-a}(x)=x,\qquad T_a(x)\in R+a\Longleftrightarrow x\in R,$$
--   $$T_a(x)\in\operatorname{relint}(R+a)\Longleftrightarrow x\in\operatorname{relint}R.$$
--   A tiling's covering, disjoint-interior, positivity, and side-bound properties are preserved. These constructions specify the orientation of geometric covariance under repointing.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/RectangularTranslation.lean, selected declaration lines 9-10, 12-14, 16-18, 24-27, 29-32, 34-37, 44-47, 49-56, 64-91, 93-115; SHA-256 6aae153157d0c3bfafbd4e3db5bcd3c0cbe879a92691fd4815efe0122fe4f751. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_FiniteRectangleIntersections
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RectangularLocalFiniteness
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportModel
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-! # Literal translation covariance of integer boundary strata -/

namespace AbelianTargets

noncomputable section

def translateCoordinates {d : ℕ} (a : Fin d → ℤ) (x : RealCoordinates d) : RealCoordinates d :=
  fun i => x i+(a i : ℝ)

@[simp] theorem translateCoordinates_neg_cancel {d : ℕ} (a : Fin d → ℤ) (x : RealCoordinates d) :
    translateCoordinates (-a) (translateCoordinates a x)=x := by
  funext i; simp [translateCoordinates]

@[simp] theorem translateCoordinates_cancel_neg {d : ℕ} (a : Fin d → ℤ) (x : RealCoordinates d) :
    translateCoordinates a (translateCoordinates (-a) x)=x := by
  funext i; simp [translateCoordinates]

namespace RectangularCell

variable {d : ℕ}

theorem mem_closedBox_translateCoordinates (R : RectangularCell d) (a : Fin d → ℤ)
    (x : RealCoordinates d) :
    translateCoordinates a x ∈ (R.translate a).closedBox ↔ x ∈ R.closedBox :=
  R.mem_closedBox_translate a x

@[simp] theorem translate_neg_cancel (R : RectangularCell d) (a : Fin d → ℤ) :
    (R.translate a).translate (-a)=R := by
  apply endpoint_pair_injective
  apply Prod.ext <;> funext i <;> simp [translate]

@[simp] theorem translate_cancel_neg (R : RectangularCell d) (a : Fin d → ℤ) :
    (R.translate (-a)).translate a=R := by
  apply endpoint_pair_injective
  apply Prod.ext <;> funext i <;> simp [translate]



theorem mem_relativeInterior_translate (R : RectangularCell d) (a : Fin d → ℤ)
    (x : RealCoordinates d) :
    translateCoordinates a x ∈ (R.translate a).relativeInterior ↔ x ∈ R.relativeInterior := by
  simp [relativeInterior,translate,translateCoordinates]

theorem faceAt_translate (R : RectangularCell d) (a : Fin d → ℤ) (x : RealCoordinates d) :
    (R.translate a).faceAt (translateCoordinates a x)=(R.faceAt x).translate a := by
  apply endpoint_pair_injective
  apply Prod.ext <;> funext i
  · simp only [faceAt,translate,translateCoordinates,Int.cast_add,add_left_inj]
    split_ifs <;> rfl
  · simp only [faceAt,translate,translateCoordinates,Int.cast_add,add_left_inj]
    split_ifs <;> rfl

end RectangularCell

namespace IntegerRectangularTiling

variable {d : ℕ} {K : Fin d → ℕ}

def translate (T : IntegerRectangularTiling d K) (a : Fin d → ℤ) : IntegerRectangularTiling d K where
  tiles := (fun R => R.translate a) '' T.tiles
  positive := by
    rintro R ⟨Q,hQ,rfl⟩ i
    dsimp [RectangularCell.translate]
    have h := T.positive Q hQ i
    omega
  cover := by
    intro z
    obtain ⟨R,hR,hz⟩ := T.cover (translateCoordinates (-a) z)
    refine ⟨R.translate a,⟨R,hR,rfl⟩,?_⟩
    have hh := (R.mem_closedBox_translate a (translateCoordinates (-a) z)).mpr hz
    change translateCoordinates a (translateCoordinates (-a) z) ∈ (R.translate a).closedBox at hh
    simpa only [translateCoordinates_cancel_neg] using hh
  interior_unique := by
    rintro R ⟨P,hP,rfl⟩ Q ⟨U,hU,rfl⟩ ⟨z,hzP,hzU⟩
    have hp : translateCoordinates (-a) z ∈ P.relativeInterior := by
      apply (P.mem_relativeInterior_translate a _).mp
      simpa only [translateCoordinates_cancel_neg] using hzP
    have hu : translateCoordinates (-a) z ∈ U.relativeInterior := by
      apply (U.mem_relativeInterior_translate a _).mp
      simpa only [translateCoordinates_cancel_neg] using hzU
    rw [T.interior_unique P hP U hU ⟨_,hp,hu⟩]
  bounded := by
    rintro R ⟨Q,hQ,rfl⟩ i
    have h := T.bounded Q hQ i
    dsimp [RectangularCell.translate]
    omega

theorem pointCell_translate (T : IntegerRectangularTiling d K) (a : Fin d → ℤ)
    (x : RealCoordinates d) :
    (T.translate a).pointCell (translateCoordinates a x)=(T.pointCell x).translate a := by
  apply RectangularCell.closedBox_injective
  ext z
  change z ∈ ((T.translate a).pointCell (translateCoordinates a x)).closedBox ↔
    z ∈ ((T.pointCell x).translate a).closedBox
  let w := translateCoordinates (-a) z
  have hzw : translateCoordinates a w=z := translateCoordinates_cancel_neg a z
  rw [←hzw,(T.pointCell x).mem_closedBox_translateCoordinates a w]
  rw [(T.translate a).mem_pointCell,T.mem_pointCell]
  constructor
  · intro h R hR hxR
    have ht : R.translate a ∈ (T.translate a).tiles := ⟨R,hR,rfl⟩
    have hx : translateCoordinates a x ∈ (R.translate a).closedBox :=
      (R.mem_closedBox_translate a x).mpr hxR
    have hh := h (R.translate a) ht hx
    rw [RectangularCell.faceAt_translate] at hh
    exact ((R.faceAt x).mem_closedBox_translate a w).mp hh
  · rintro h R ⟨Q,hQ,rfl⟩ hxR
    have hx : x ∈ Q.closedBox := (Q.mem_closedBox_translate a x).mp hxR
    rw [RectangularCell.faceAt_translate]
    exact ((Q.faceAt x).mem_closedBox_translate a w).mpr (h Q hQ hx)

end IntegerRectangularTiling

end

end AbelianTargets


