-- Prove2me | solution 1 for Kourovka.CentralLattice.map_mem_saturation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:36:45.578976+00:00
-- url     : https://prove2.me/submissions/b9aaf252-13f4-4848-b7dd-3dbd52728a5a

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
namespace Kourovka.CentralLattice
theorem _root_.solution (D : Submodule ℤ M) (u : M →ₗ[ℤ] M)
    (hu : ∀ x ∈ D, u x ∈ D) {x : M} (hx : x ∈ saturation D) :
    u x ∈ saturation D := by
  obtain ⟨n, hn, hnx⟩ := (mem_saturation D x).mp hx
  exact (mem_saturation D (u x)).mpr ⟨n, hn, by simpa using hu _ hnx⟩
end Kourovka.CentralLattice
