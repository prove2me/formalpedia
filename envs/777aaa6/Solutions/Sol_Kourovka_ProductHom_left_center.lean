-- Prove2me | solution 1 for Kourovka.ProductHom.left_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:29:42.604805+00:00
-- url     : https://prove2.me/submissions/c7e63629-4c8d-4cbb-88c6-50ea055a3312

import Definitions.Def_Kourovka_Hopfian
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Prod
import Definitions.Def_Kourovka_Components

set_option autoImplicit true
open Kourovka
variable {A B K : Type*} [Group A] [Group B] [Group K]
open Kourovka.ProductHom
namespace Kourovka.ProductHom
theorem _root_.solution (f : A × B →* K) (hf : Function.Surjective f)
    {a : A} (ha : a ∈ Subgroup.center A) : left f a ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff] at ha ⊢
  intro k
  obtain ⟨⟨x, y⟩, rfl⟩ := hf k
  change f (x, y) * f (a, 1) = f (a, 1) * f (x, y)
  rw [← map_mul, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_one, one_mul, ha x]
end Kourovka.ProductHom
