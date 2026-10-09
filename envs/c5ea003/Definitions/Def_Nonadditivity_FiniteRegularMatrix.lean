-- Prove2me | Definitions.Def_Nonadditivity_FiniteRegularMatrix
-- name    : Nonadditivity_FiniteRegularMatrix
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:34:30.038644+00:00
-- url     : https://prove2.me/theorems/d439eada-1b1f-4a52-a077-2a94010aeede
-- title:
--   Unitary matrices of the finite regular representation
-- statement:
--   For a finite group $H$, let $L_g$ be the complex permutation matrix representing left translation $h\mapsto gh$ on the basis indexed by $H$. The assignments $g\mapsto L_g$ form a matrix monoid homomorphism and a unitary-group homomorphism. They satisfy
--   $$L_g^*=L_{g^{-1}},\qquad \operatorname{Tr}L_g=|H|\,\mathbf1_{g=1}.$$
--   A nonidentity translation fixes no basis vector, giving the exact regular character. These concrete unitary matrices realize bounded free-word separation as exact normalized trace matching in finite dimension.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/FiniteRegularMatrix.lean#L16-L61

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-! The actual finite regular representation, including its exact normalized trace. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.FiniteRegularMatrix
open scoped Matrix
variable (H : Type*) [Group H] [Fintype H] [DecidableEq H]

/-- Left translation on the basis of the finite group algebra. -/
def regularHom : H →* Matrix H H ℂ :=
  (Matrix.permMatrixHom : Equiv.Perm H →* Matrix H H ℂ).comp (MulAction.toPermHom H H)

theorem regularHom_conjTranspose (g : H) :
    (regularHom H g).conjTranspose = regularHom H g⁻¹ := by
  change ((((MulAction.toPermHom H H) g)⁻¹).permMatrix ℂ).conjTranspose =
    (((MulAction.toPermHom H H) g⁻¹)⁻¹).permMatrix ℂ
  rw [Matrix.conjTranspose_permMatrix,map_inv]

def regularUnitaryHom : H →* unitary (Matrix H H ℂ) where
  toFun g := ⟨regularHom H g, by
    apply Unitary.mem_iff.mpr
    simp only [Matrix.star_eq_conjTranspose,regularHom_conjTranspose,←map_mul,
      inv_mul_cancel,mul_inv_cancel,map_one,and_self]⟩
  map_one' := Subtype.ext (map_one (regularHom H))
  map_mul' g h := Subtype.ext (map_mul (regularHom H) g h)

/-- Alias with the concise representation name. -/
abbrev regularUnitary := regularUnitaryHom H

@[simp] theorem coe_regularUnitaryHom (g : H) :
    (regularUnitaryHom H g : Matrix H H ℂ) = regularHom H g := rfl

/-- A nonidentity group element fixes no basis vector in the regular action. -/
theorem regularHom_trace (g : H) :
    (regularHom H g).trace = (Fintype.card H : ℂ) * (if g=1 then 1 else 0) := by
  classical
  by_cases hg : g=1
  · subst g
    simp
  · change ((((MulAction.toPermHom H H) g)⁻¹).permMatrix ℂ).trace = _
    rw [←map_inv (MulAction.toPermHom H H),Matrix.trace_permutation]
    have hfix : Function.fixedPoints ((MulAction.toPermHom H H) g⁻¹) = ∅ := by
      ext x
      simp only [Function.mem_fixedPoints,Set.mem_empty_iff_false,iff_false]
      intro hx
      change g⁻¹*x=x at hx
      have hi : g⁻¹=1 := mul_right_cancel (hx.trans (one_mul x).symm)
      exact hg (inv_eq_one.mp hi)
    rw [hfix]
    simp [hg]

@[simp] theorem regularUnitaryHom_trace (g : H) :
    (regularUnitaryHom H g : Matrix H H ℂ).trace =
      (Fintype.card H : ℂ) * (if g=1 then 1 else 0) := regularHom_trace H g

end Nonadditivity.FiniteRegularMatrix


