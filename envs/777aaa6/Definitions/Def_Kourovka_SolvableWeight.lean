-- Prove2me | Definitions.Def_Kourovka_SolvableWeight
-- name    : Kourovka_SolvableWeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:28:53.498647+00:00
-- url     : https://prove2.me/theorems/00f303e2-8b00-47fd-a44b-977a73d30d30
-- title:
--   Solvable Weight
-- statement:
--   Definitions and structural lemmas for Solvable Weight, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/SolvableWeight.lean

import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.Algebra.Group.Equiv.TypeTags
set_option autoImplicit true
namespace Kourovka
namespace SolvableWeight
variable (G H : Type*) [Group G] [Group H]
def abelianizationProd : Abelianization (G × H) ≃*
    Abelianization G × Abelianization H where
  toFun := Abelianization.lift
    ((Abelianization.of.comp (MonoidHom.fst G H)).prod
      (Abelianization.of.comp (MonoidHom.snd G H)))
  invFun := (Abelianization.map (MonoidHom.inl G H)).coprod
    (Abelianization.map (MonoidHom.inr G H))
  left_inv x := by
    obtain ⟨⟨g, h⟩, rfl⟩ := QuotientGroup.mk_surjective x
    change Abelianization.of (g, (1 : H)) * Abelianization.of ((1 : G), h) =
      Abelianization.of (g, h)
    rw [← map_mul]
    simp
  right_inv x := by
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x.1
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective x.2
    rcases x with ⟨x, y⟩
    dsimp at hg hh
    subst x y
    change Abelianization.lift
      ((Abelianization.of.comp (MonoidHom.fst G H)).prod
        (Abelianization.of.comp (MonoidHom.snd G H)))
      (Abelianization.of (g, (1 : H)) * Abelianization.of ((1 : G), h)) = _
    rw [← map_mul]
    change (Abelianization.of (g * 1), Abelianization.of (1 * h)) = _
    simp only [mul_one, one_mul]
    rfl
  map_mul' x y := map_mul _ x y
instance abelianizationFG [Group.FG G] : Group.FG (Abelianization G) :=
  Group.fg_of_surjective (f := Abelianization.of) QuotientGroup.mk_surjective
instance abelianizationModuleFinite [Group.FG G] :
    Module.Finite ℤ (Additive (Abelianization G)) :=
  Module.Finite.iff_addGroup_fg.mpr inferInstance
noncomputable def weight : ℕ := AbelianWeight.weight (Additive (Abelianization G))
end SolvableWeight
end Kourovka


