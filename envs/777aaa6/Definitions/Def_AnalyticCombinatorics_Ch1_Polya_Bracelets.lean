-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_Polya_Bracelets
-- name    : AnalyticCombinatorics_Ch1_Polya_Bracelets
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-24T23:49:48.161605+00:00
-- url     : https://prove2.me/theorems/a447b860-4c33-4b2d-99f1-61f5095569d6
-- title:
--   Dihedral actions and reflection fixed points
-- statement:
--   For every natural $n$, the dihedral group acts on residue positions by $r_i\cdot x=x-i$ and $sr_i\cdot x=i-x$. The foundation constructs this action and identifies the vertices fixed by $sr_i$ with the solutions of $x+x=i$. It also supplies finite orbit quotients and finite subtypes when their underlying object sets are finite. The binary-bracelet counting theorem separately requires $n>0$ and uses the induced action on two-color assignments; exchanging the two colors is not an additional equivalence.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/Polya/Bracelets.lean
--   Source code license: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Binary bracelets

This file applies the Pólya enumeration theorem to binary colorings of `ZMod n`
under the dihedral action.  With Mathlib's multiplication convention for
`DihedralGroup`, the compatible left action is `r i : x ↦ x - i` and
`sr i : x ↦ i - x`.
-/

namespace AnalyticCombinatorics.Ch1.Polya.Bracelets

open scoped BigOperators

attribute [local instance] arrowAction

noncomputable local instance orbitRelDecidableRel {G X : Type*} [Group G] [MulAction G X] :
    DecidableRel (MulAction.orbitRel G X).r :=
  Classical.decRel _

noncomputable local instance orbitQuotientFintype {G X : Type*} [Group G] [MulAction G X]
    [Fintype X] :
    Fintype (MulAction.orbitRel.Quotient G X) :=
  Quotient.fintype (MulAction.orbitRel G X)

noncomputable local instance subtypeFintypeClassical {X : Type*} [Fintype X] (p : X → Prop) :
    Fintype {x // p x} :=
  @Subtype.fintype X p (Classical.decPred p) inferInstance

section Action

/-- The faithful-on-rotations dihedral action on vertices.  Mathlib's multiplication rules force
rotations to act as `x - i` for a left action with reflections `x ↦ i - x`. -/
instance dihedralZModMulAction (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  smul g x :=
    match g with
    | DihedralGroup.r i => x - i
    | DihedralGroup.sr i => i - x
  one_smul x := by
    change x - (0 : ZMod n) = x
    simp
  mul_smul g h x := by
    cases g with
    | r i =>
        cases h with
        | r j =>
            change x - (i + j) = (x - j) - i
            ring
        | sr j =>
            change (j - i) - x = (j - x) - i
            ring
    | sr i =>
        cases h with
        | r j =>
            change (i + j) - x = i - (x - j)
            ring
        | sr j =>
            change x - (j - i) = i - (j - x)
            ring

@[simp]
theorem dihedral_r_smul (n : ℕ) (i x : ZMod n) :
    (DihedralGroup.r i : DihedralGroup n) • x = x - i :=
  rfl

@[simp]
theorem dihedral_sr_smul (n : ℕ) (i x : ZMod n) :
    (DihedralGroup.sr i : DihedralGroup n) • x = i - x :=
  rfl

end Action

section FixedPoints

variable {n : ℕ}

/-- Reflection fixed points are exactly the solutions of `x + x = i`. -/
noncomputable def reflectionFixedByEquivAddSelf (i : ZMod n) :
    MulAction.fixedBy (ZMod n) (DihedralGroup.sr i : DihedralGroup n) ≃
      {x : ZMod n // x + x = i} where
  toFun x := by
    refine ⟨x.1, ?_⟩
    have hx : i - x.1 = x.1 := x.2
    rw [sub_eq_iff_eq_add] at hx
    simpa [add_comm] using hx.symm
  invFun x := by
    refine ⟨x.1, ?_⟩
    rw [MulAction.mem_fixedBy]
    rw [dihedral_sr_smul, sub_eq_iff_eq_add]
    simpa [add_comm] using x.2.symm
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl

end FixedPoints

section ReflectionOrbits

variable {n : ℕ} [NeZero n]

end ReflectionOrbits

section RotationOrbits

variable {n : ℕ} [NeZero n]

end RotationOrbits

section Sums

variable {n : ℕ} [NeZero n]

end Sums

end AnalyticCombinatorics.Ch1.Polya.Bracelets


