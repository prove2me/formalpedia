-- Prove2me | solution 1 for Kourovka.CentralLattice.eq_on_torsion_of_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:46.370281+00:00
-- url     : https://prove2.me/submissions/8e9a06d5-ced1-4747-9cdd-53a22e79cdf0

import Definitions.Def_Kourovka_DerivedReduction
import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective
import Definitions.Def_Kourovka_CentralLattice
import Theorems.Thm_Kourovka_CentralLattice_smul_mem_torsion_iff

set_option autoImplicit true
noncomputable section
open scoped nonZeroDivisors
open Kourovka Kourovka.CentralLattice
variable {M Z : Type*} [AddCommGroup M] [AddCommGroup Z]
namespace Kourovka.CentralLattice
theorem _root_.solution (u : M →ₗ[ℤ] M) (d : ℤ) (hd : d ≠ 0)
    (hkill : ∀ x ∈ Submodule.torsion ℤ M, d • x = 0)
    (hcong : ∀ x, ∃ y, u x - x = d • y) :
    ∀ x ∈ Submodule.torsion ℤ M, u x = x := by
  intro x hx
  obtain ⟨y, hy⟩ := hcong x
  have hdy : d • y ∈ Submodule.torsion ℤ M :=
    hy ▸ (Submodule.torsion ℤ M).sub_mem (map_torsion u hx) hx
  have hzero := hkill y ((smul_mem_torsion_iff hd y).mp hdy)
  exact sub_eq_zero.mp (hy.trans hzero)
end Kourovka.CentralLattice
