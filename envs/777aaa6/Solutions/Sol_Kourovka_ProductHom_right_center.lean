-- Prove2me | solution 1 for Kourovka.ProductHom.right_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:28:53.820641+00:00
-- url     : https://prove2.me/submissions/260073fd-36d3-4929-9c3b-b3e056f2519b

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
    {b : B} (hb : b ∈ Subgroup.center B) : right f b ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff] at hb ⊢
  intro k
  obtain ⟨⟨x, y⟩, rfl⟩ := hf k
  change f (x, y) * f (1, b) = f (1, b) * f (x, y)
  rw [← map_mul, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_one, one_mul, hb y]
end Kourovka.ProductHom
