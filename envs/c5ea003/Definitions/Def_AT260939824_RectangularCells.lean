-- Prove2me | Definitions.Def_AT260939824_RectangularCells
-- name    : AT260939824_RectangularCells
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:43:55.73288+00:00
-- url     : https://prove2.me/theorems/5c670d1a-254b-41c3-afd1-3c150d365995
-- title:
--   Integer rectangular cells, relative interiors, faces, and rank
-- statement:
--   For $d\in\mathbb N$, an integer rectangular cell is specified by endpoint vectors $\ell,u\in\mathbb Z^d$ satisfying $\ell_i\le u_i$. Its closed box, varying axes, and rank are
--   $$R=\prod_i[\ell_i,u_i],\qquad A(R)=\{i:\ell_i<u_i\},\qquad\operatorname{rank}R=|A(R)|.$$
--   Its relative interior uses open intervals on varying axes and the fixed coordinate $\ell_i$ on collapsed axes; its relative boundary is the closed box minus this relative interior. The face at a point is obtained by collapsing every coordinate where the point equals an endpoint. For a point of the closed box, this face contains the point in its relative interior. Translation by $a\in\mathbb Z^d$ adds $a$ to both endpoint vectors and preserves rank. Degenerate cells and $d=0$ are included.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/RectangularCells.lean, selected declaration lines 19-23, 29-30, 32-34, 36-37, 39, 41-42, 44-52, 54-64, 71-80, 82-92, 94-101, 103-120, 151-154, 156-159, 161-163; SHA-256 11ead30fef909b89b90954f8c0b6787adb082c345aefda06b1d65394ee4adafe. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_Probability
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

/-!
# Integer rectangular cells and their point faces

These are literal closed rectangles, including degenerate coordinates. The
relative interior keeps a degenerate coordinate fixed. `faceAt` is the smallest
coordinate face containing a given point, rather than a chosen abstract cell.
-/

namespace AbelianTargets

noncomputable section

structure RectangularCell (d : ℕ) where
  lower : Fin d → ℤ
  upper : Fin d → ℤ
  ordered : ∀ i, lower i ≤ upper i
  deriving DecidableEq

namespace RectangularCell

variable {d : ℕ}

def closedBox (R : RectangularCell d) : Set (RealCoordinates d) :=
  {x | ∀ i, (R.lower i : ℝ) ≤ x i ∧ x i ≤ (R.upper i : ℝ)}

def relativeInterior (R : RectangularCell d) : Set (RealCoordinates d) :=
  {x | ∀ i, if R.lower i = R.upper i then x i = (R.lower i : ℝ)
    else (R.lower i : ℝ) < x i ∧ x i < (R.upper i : ℝ)}

def varyingAxes (R : RectangularCell d) : Finset (Fin d) :=
  Finset.univ.filter (fun i => R.lower i < R.upper i)

def rank (R : RectangularCell d) : ℕ := R.varyingAxes.card

def boundary (R : RectangularCell d) : Set (RealCoordinates d) :=
  R.closedBox \ R.relativeInterior

theorem relativeInterior_subset (R : RectangularCell d) :
    R.relativeInterior ⊆ R.closedBox := by
  intro x hx i
  have hi := hx i
  by_cases h : R.lower i = R.upper i
  · simp only [h, if_true] at hi
    simpa [hi, h]
  · simp only [h, if_false] at hi
    exact ⟨hi.1.le, hi.2.le⟩

theorem isClosed_closedBox (R : RectangularCell d) : IsClosed R.closedBox := by
  change IsClosed {x : RealCoordinates d | ∀ i,
    (R.lower i : ℝ) ≤ x i ∧ x i ≤ (R.upper i : ℝ)}
  have he : {x : RealCoordinates d | ∀ i,
      (R.lower i : ℝ) ≤ x i ∧ x i ≤ (R.upper i : ℝ)} =
      ⋂ i, {x : RealCoordinates d | (R.lower i : ℝ) ≤ x i ∧ x i ≤ (R.upper i : ℝ)} := by
    ext x; simp
  rw [he]
  exact isClosed_iInter fun i =>
    (isClosed_le continuous_const (continuous_apply i : Continuous (fun x : RealCoordinates d => x i))).inter
      (isClosed_le (continuous_apply i : Continuous (fun x : RealCoordinates d => x i)) continuous_const)



theorem relativeInterior_nonempty (R : RectangularCell d) :
    R.relativeInterior.Nonempty := by
  refine ⟨fun i => ((R.lower i : ℝ) + (R.upper i : ℝ)) / 2, ?_⟩
  intro i
  by_cases h : R.lower i = R.upper i
  · simp [h]
  · simp only [h, if_false]
    have hi : (R.lower i : ℝ) < (R.upper i : ℝ) := by
      exact_mod_cast lt_of_le_of_ne (R.ordered i) h
    constructor <;> linarith

def faceAt (R : RectangularCell d) (x : RealCoordinates d) : RectangularCell d where
  lower i := if x i = (R.upper i : ℝ) then R.upper i else R.lower i
  upper i := if x i = (R.lower i : ℝ) then R.lower i else R.upper i
  ordered i := by
    split_ifs with hu hl hl
    · have h : R.lower i = R.upper i := by
        exact_mod_cast (hl.symm.trans hu)
      omega
    · exact le_rfl
    · exact le_rfl
    · exact R.ordered i

theorem faceAt_subset (R : RectangularCell d) (x : RealCoordinates d) :
    (R.faceAt x).closedBox ⊆ R.closedBox := by
  intro y hy i
  have hi := hy i
  have h := R.ordered i
  have h' : (R.lower i : ℝ) ≤ (R.upper i : ℝ) := by exact_mod_cast h
  simp only [faceAt] at hi
  split_ifs at hi <;> constructor <;> linarith

theorem mem_relativeInterior_faceAt (R : RectangularCell d)
    {x : RealCoordinates d} (hx : x ∈ R.closedBox) :
    x ∈ (R.faceAt x).relativeInterior := by
  intro i
  have hi := hx i
  by_cases hu : x i = (R.upper i : ℝ)
  · by_cases hl : x i = (R.lower i : ℝ)
    · have he : R.lower i = R.upper i := by exact_mod_cast hl.symm.trans hu
      simp [relativeInterior, faceAt, hu, hl, he]
    · simp [relativeInterior, faceAt, hu, hl]
  · by_cases hl : x i = (R.lower i : ℝ)
    · simp [faceAt, hu, hl, eq_comm]
    · have he : R.lower i ≠ R.upper i := by
        intro he
        have hi' : (R.lower i : ℝ) = (R.upper i : ℝ) := by rw [he]
        exact hl (le_antisymm (hi.2.trans hi'.symm.le) hi.1)
      simp only [relativeInterior, faceAt, hu, hl, if_false, he]
      exact ⟨lt_of_le_of_ne hi.1 (Ne.symm hl), lt_of_le_of_ne hi.2 hu⟩





def translate (R : RectangularCell d) (a : Fin d → ℤ) : RectangularCell d where
  lower i := R.lower i + a i
  upper i := R.upper i + a i
  ordered i := by have h := R.ordered i; omega

theorem mem_closedBox_translate (R : RectangularCell d) (a : Fin d → ℤ)
    (x : RealCoordinates d) :
    (fun i => x i + (a i : ℝ)) ∈ (R.translate a).closedBox ↔ x ∈ R.closedBox := by
  simp [closedBox, translate]

theorem rank_translate (R : RectangularCell d) (a : Fin d → ℤ) :
    (R.translate a).rank = R.rank := by
  simp [rank, varyingAxes, translate]

end RectangularCell

end

end AbelianTargets


