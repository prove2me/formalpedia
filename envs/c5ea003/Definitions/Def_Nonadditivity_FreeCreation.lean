-- Prove2me | Definitions.Def_Nonadditivity_FreeCreation
-- name    : Nonadditivity_FreeCreation
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:35:54.558391+00:00
-- url     : https://prove2.me/theorems/a6281ab3-6c1a-49b1-8ed5-8b9c612c1160
-- title:
--   Coordinate projections and creation operators in a free group
-- statement:
--   For a free group on generators indexed by a type $A$, a signed letter is a generator together with its sign. Flipping the sign gives the inverse group element. The cone of a letter consists of group elements whose reduced word begins with that letter. The proved cancellation and disjointness identities provide the coordinate subsets used to split regular shifts into creation and annihilation components. On $\ell^2(F_A;\mathbb C)$, coordinate masks retain a prescribed subset and creation shifts translate while discarding coordinates where the new letter cancels. Their coordinate formulas and boundedness estimates accompany the definitions.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/FreeCreation.lean#L29-L207

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FreeModel
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/





/-! # Concrete reduced-word projections and free creation operators

These operators act on the actual square-summable functions used by FreeModel.
They are the cancellation decomposition underlying the length-two estimate.
-/

noncomputable section

namespace Nonadditivity.FreeCreation

open Nonadditivity.FreeModel
open scoped BigOperators InnerProductSpace

attribute [local instance] Classical.propDecidable

section Mask

variable {G : Type*}

/-- An actual coordinate projection on the regular Hilbert space. -/
def maskFunction (P : G → Prop) (f : Hilbert G) : Hilbert G :=
  ⟨fun x => if P x then f x else 0, by
    classical
    apply memℓp_gen
    apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
      (fun x => ?_) (f.property.summable (by norm_num))
    split_ifs <;> simp⟩

@[simp] theorem maskFunction_apply (P : G → Prop) (f : Hilbert G) (x : G) :
    maskFunction P f x = if P x then f x else 0 := rfl

theorem maskFunction_norm_le (P : G → Prop) (f : Hilbert G) :
    ‖maskFunction P f‖ ≤ ‖f‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg f)
  rw [lp.norm_rpow_eq_tsum (by norm_num)]
  apply Summable.tsum_le_tsum
    (fun x => ?_) ((maskFunction P f).property.summable (by norm_num))
    (f.property.summable (by norm_num))
  classical
  simp only [maskFunction_apply]
  split_ifs <;> simp

def maskLinear (P : G → Prop) : Hilbert G →ₗ[ℂ] Hilbert G where
  toFun := maskFunction P
  map_add' := by
    intro f h
    ext x
    classical
    simp only [maskFunction_apply, lp.coeFn_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' := by
    intro c f
    ext x
    classical
    simp only [maskFunction_apply, lp.coeFn_smul, Pi.smul_apply]
    split_ifs <;> simp

/-- The coordinate mask is a genuine bounded linear projection. -/
def mask (P : G → Prop) : Hilbert G →L[ℂ] Hilbert G :=
  (maskLinear P).mkContinuous 1 (by
    intro f
    simpa [maskLinear] using maskFunction_norm_le P f)

@[simp] theorem mask_apply (P : G → Prop) (f : Hilbert G) (x : G) :
    mask P f x = if P x then f x else 0 := rfl







end Mask

section Word

variable {α : Type*} [DecidableEq α]

abbrev Letter (α : Type*) := α × Bool

def flip (s : Letter α) : Letter α := (s.1, !s.2)

omit [DecidableEq α] in
@[simp] theorem flip_flip (s : Letter α) : flip (flip s) = s := by
  rcases s with ⟨a,b⟩
  cases b <;> rfl

def letter (s : Letter α) : FreeGroup α :=
  if s.2 then FreeGroup.of s.1 else (FreeGroup.of s.1)⁻¹

omit [DecidableEq α] in
@[simp] theorem letter_flip (s : Letter α) : letter (flip s) = (letter s)⁻¹ := by
  rcases s with ⟨a,b⟩
  cases b <;> simp [letter, flip]

@[simp] theorem letter_toWord (s : Letter α) : (letter s).toWord = [s] := by
  rcases s with ⟨a,b⟩
  cases b <;> simp [letter, FreeGroup.invRev]

/-- Words whose reduced first letter is the specified letter. -/
def Cone (s : Letter α) (x : FreeGroup α) : Prop := ∃ t, x.toWord = s :: t

theorem cone_disjoint {s t : Letter α} (hne : s ≠ t) (x : FreeGroup α) :
    ¬ (Cone s x ∧ Cone t x) := by
  rintro ⟨⟨u,hu⟩, ⟨v,hv⟩⟩
  exact hne (List.cons.inj (hu.symm.trans hv)).1

theorem cone_shift_iff (s : Letter α) (x : FreeGroup α) :
    Cone s (letter s * x) ↔ ¬ Cone (flip s) x := by
  have hword : (letter s * x).toWord = FreeGroup.reduce (s :: x.toWord) := by
    rw [FreeGroup.toWord_mul, letter_toWord]
    rfl
  cases hx : x.toWord with
  | nil =>
    simp [Cone, hword, hx, FreeGroup.reduce]
  | cons t tail =>
    have hred : FreeGroup.reduce (t :: tail) = t :: tail := by
      rw [← hx]
      exact FreeGroup.reduce_toWord x
    unfold Cone
    rw [hword, FreeGroup.reduce.cons, hx, hred]
    by_cases he : s.1 = t.1 ∧ s.2 = !t.2
    · have ht : t = flip s := by
        rcases s with ⟨a,b⟩
        rcases t with ⟨c,d⟩
        cases b <;> cases d <;> simp_all [flip]
      simp only [he]
      have hn : ¬ ∃ u, tail = s :: u := by
        rintro ⟨u, rfl⟩
        have hr := FreeGroup.isReduced_toWord (x := x)
        rw [hx, FreeGroup.isReduced_cons_cons] at hr
        have hb := hr.1 (by simp [ht, flip])
        have hb' : (flip s).2 = s.2 := by simpa [ht] using hb
        rcases s with ⟨a,b⟩
        cases b <;> simp [flip] at hb'
      simp [ht, hn]
    · have ht : t ≠ flip s := by
        intro ht
        apply he
        rw [ht]
        rcases s with ⟨a,b⟩
        cases b <;> simp [flip]
      simp [he, ht]

end Word

section Operators

variable {α : Type*} [DecidableEq α]





/-- A letter creation shift, retaining only words where the new letter does
not cancel. Its range consists of words with that reduced first letter. -/
def creation (s : Letter α) : Hilbert (FreeGroup α) →L[ℂ] Hilbert (FreeGroup α) :=
  (mask (Cone s)).comp (leftRegular (letter s))

@[simp] theorem creation_apply (s : Letter α) (f : Hilbert (FreeGroup α))
    (x : FreeGroup α) :
    creation s f x = if Cone s x then f ((letter s)⁻¹ * x) else 0 := rfl

/-- Creation is equally the full shift restricted to its noncancelling input cone. -/
theorem creation_domain (s : Letter α) :
    creation s = (leftRegular (letter s)).comp (mask (fun x => ¬ Cone (flip s) x)) := by
  ext f x
  have hc : Cone s x ↔ ¬ Cone (flip s) ((letter s)⁻¹ * x) := by
    simpa [mul_assoc] using cone_shift_iff s ((letter s)⁻¹ * x)
  simp [creation_apply, ContinuousLinearMap.comp_apply, leftRegular_apply, mask_apply, hc]















end Operators

end Nonadditivity.FreeCreation


