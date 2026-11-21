-- Prove2me | Theorems.Thm_Kourovka_CentralLattice_exists_correction_of_congr
-- name    : Kourovka.CentralLattice.exists_correction_of_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:34.238179+00:00
-- url     : https://prove2.me/theorems/30e9c3f4-8fe7-405a-972d-051a97435fdc
-- title:
--   Central Lattice: exists correction of congr
-- statement:
--   Lift the free-quotient correction to the full finitely generated abelian group.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralLattice.lean#L214-L269
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralLattice.lean#L214-L269

import Definitions.Def_Kourovka_DerivedReduction
import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective
import Definitions.Def_Kourovka_CentralLattice
set_option autoImplicit true
noncomputable section
open scoped nonZeroDivisors
open Kourovka Kourovka.CentralLattice
variable {M Z : Type*} [AddCommGroup M] [AddCommGroup Z]

theorem Kourovka.CentralLattice.exists_correction_of_congr [Module.Finite ℤ M]
    (c : Z →ₗ[ℤ] M) (u : M →ₗ[ℤ] M) (d : ℤ) (hd : d ≠ 0)
    (hden : ∀ x ∈ saturation (LinearMap.range ((Submodule.torsion ℤ M).mkQ.comp c)),
      d • x ∈ LinearMap.range ((Submodule.torsion ℤ M).mkQ.comp c))
    (hkill : ∀ x ∈ Submodule.torsion ℤ M, d • x = 0)
    (hu : ∀ x ∈ LinearMap.range c, u x ∈ LinearMap.range c)
    (hrow : ∀ y, ∃ x z, u x + c z = y)
    (hcong : ∀ x, ∃ y, u x - x = d • y) :
    ∃ h : M →ₗ[ℤ] Z, Function.Surjective (u + c.comp h) := by sorry
