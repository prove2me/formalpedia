-- Prove2me | Definitions.Def_Kourovka_Cofinality_CofinalCover
-- name    : Kourovka_Cofinality_CofinalCover
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:42:13.389155+00:00
-- url     : https://prove2.me/theorems/b61c1d28-9dd9-4c50-accb-0a85bc611c40
-- title:
--   Cofinal Cover
-- statement:
--   Definitions and structural lemmas for Cofinal Cover, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalCover.lean

import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.CofinalCover
variable {G H Q : Type} [Group G] [Group H] [Group Q]
def pullback (p : G →* Q) (q : H →* Q) : Subgroup (G × H) where
  carrier := {x | p x.1 = q x.2}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change p (x.1 * y.1) = q (x.2 * y.2)
    rw [map_mul, map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    change p x.1⁻¹ = q x.2⁻¹
    rw [map_inv, map_inv, hx]
def first (p : G →* Q) (q : H →* Q) : pullback p q →* G :=
  (MonoidHom.fst G H).comp (pullback p q).subtype
def second (p : G →* Q) (q : H →* Q) : pullback p q →* H :=
  (MonoidHom.snd G H).comp (pullback p q).subtype
@[simp] theorem first_apply (p : G →* Q) (q : H →* Q) (x : pullback p q) :
    first p q x = x.val.1 := rfl
@[simp] theorem second_apply (p : G →* Q) (q : H →* Q) (x : pullback p q) :
    second p q x = x.val.2 := rfl
def firstKernelEquiv (p : G →* Q) (q : H →* Q) : (first p q).ker ≃* q.ker where
  toFun x := ⟨x.val.val.2, by
    have hx : x.val.val.1 = 1 := x.property
    change q x.val.val.2 = 1
    rw [← x.val.property, hx, map_one]⟩
  invFun h := ⟨⟨(1, h.val), by
    change p 1 = q h.val
    rw [map_one]
    exact h.property.symm⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (show x.val.val.1 = 1 from x.property).symm
    · rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
def secondKernelEquiv (p : G →* Q) (q : H →* Q) : (second p q).ker ≃* p.ker where
  toFun x := ⟨x.val.val.1, by
    have hx : x.val.val.2 = 1 := x.property
    change p x.val.val.1 = 1
    rw [x.val.property, hx, map_one]⟩
  invFun g := ⟨⟨(g.val, 1), by
    change p g.val = q 1
    rw [map_one]
    exact g.property⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (show x.val.val.2 = 1 from x.property).symm
  right_inv _ := rfl
  map_mul' _ _ := rfl
noncomputable def abelianQuotientMap {α : Type} (R : List (FreeGroup α)) :
    Multiplicative (FreeAbelianGroup α) →* Abelianization (PresentedGroup {r | r ∈ R}) :=
  (FreeAbelianGroup.lift (fun a => Additive.ofMul
    (Abelianization.of (PresentedGroup.of (rels := {r | r ∈ R}) a)))).toMultiplicativeLeft
end Kourovka.MetabelianEnumeration.CofinalCover


