-- Prove2me | Definitions.Def_Kourovka_Components
-- name    : Kourovka_Components
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:28:18.554148+00:00
-- url     : https://prove2.me/theorems/80118f06-0cf2-494c-a705-d713d8d4c107
-- title:
--   Components
-- statement:
--   Definitions and structural lemmas for Components, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Components.lean

import Definitions.Def_Kourovka_Hopfian
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Prod
set_option autoImplicit true
namespace Kourovka
variable {A B K : Type*} [Group A] [Group B] [Group K]
namespace ProductHom
def left (f : A × B →* K) : A →* K := f.comp (MonoidHom.inl A B)
def right (f : A × B →* K) : B →* K := f.comp (MonoidHom.inr A B)
@[simp] theorem left_apply (f : A × B →* K) (a : A) : left f a = f (a, 1) := rfl
@[simp] theorem right_apply (f : A × B →* K) (b : B) : right f b = f (1, b) := rfl
end ProductHom
def centralCorrection (u : A →* A) (h : A →* Subgroup.center A) : A →* A where
  toFun a := u a * h a
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, Subgroup.coe_mul]
    have hc := Subgroup.mem_center_iff.mp (h a).property (u b)
    calc
      (u a * u b) * (↑(h a) * ↑(h b)) = u a * (u b * ↑(h a)) * ↑(h b) := by
        simp only [mul_assoc]
      _ = u a * (↑(h a) * u b) * ↑(h b) := by rw [hc]
      _ = (u a * ↑(h a)) * (u b * ↑(h b)) := by simp only [mul_assoc]
end Kourovka


