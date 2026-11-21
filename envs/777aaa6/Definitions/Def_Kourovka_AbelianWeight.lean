-- Prove2me | Definitions.Def_Kourovka_AbelianWeight
-- name    : Kourovka_AbelianWeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:28:16.356996+00:00
-- url     : https://prove2.me/theorems/50bf8734-db6a-4d13-806c-7fa887e238e2
-- title:
--   Abelian Weight
-- statement:
--   Definitions and structural lemmas for Abelian Weight, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/AbelianWeight.lean

import Definitions.Def_Kourovka_Hopfian
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Tactic.Linarith
set_option autoImplicit true
namespace Kourovka
namespace AbelianWeight
variable (M N : Type*) [AddCommGroup M] [AddCommGroup N]
instance torsionFinite [Module.Finite ℤ M] : Finite (Submodule.torsion ℤ M) :=
  Module.finite_of_fg_torsion _ (Submodule.torsion_isTorsion (R := ℤ) (M := M))
noncomputable def weight : ℕ :=
  Module.finrank ℤ M + Nat.card (Submodule.torsion ℤ M) - 1
def torsionProdEquiv : Submodule.torsion ℤ (M × N) ≃
    (Submodule.torsion ℤ M) × (Submodule.torsion ℤ N) where
  toFun x :=
    (⟨x.val.1, by
      obtain ⟨r, hr⟩ := x.property
      exact ⟨r, congrArg Prod.fst hr⟩⟩,
     ⟨x.val.2, by
      obtain ⟨r, hr⟩ := x.property
      exact ⟨r, congrArg Prod.snd hr⟩⟩)
  invFun x := ⟨(x.1.val, x.2.val), by
    obtain ⟨r, hr⟩ := x.1.property
    obtain ⟨s, hs⟩ := x.2.property
    refine ⟨r * s, ?_⟩
    apply Prod.ext
    · change (r * s) • x.1.val = 0
      rw [mul_comm r s, mul_smul, hr, smul_zero]
    · change (r * s) • x.2.val = 0
      rw [mul_smul, hs, smul_zero]⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
def torsionCongr (e : M ≃+ N) : Submodule.torsion ℤ M ≃ Submodule.torsion ℤ N where
  toFun x := ⟨e x, by
    obtain ⟨r, hr⟩ := x.property
    refine ⟨r, ?_⟩
    change (r : ℤ) • (x : M) = 0 at hr
    change (r : ℤ) • e x = 0
    rw [← map_zsmul, hr, map_zero]⟩
  invFun y := ⟨e.symm y, by
    obtain ⟨r, hr⟩ := y.property
    refine ⟨r, ?_⟩
    change (r : ℤ) • (y : N) = 0 at hr
    change (r : ℤ) • e.symm y = 0
    rw [← map_zsmul, hr, map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
end AbelianWeight
end Kourovka


