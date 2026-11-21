-- Prove2me | solution 1 for Kourovka.CentralLattice.abelianMap_centralCorrection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:14.370985+00:00
-- url     : https://prove2.me/submissions/7b9541ee-8d58-4766-8a71-ee8251a8c845

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
variable {G : Type*} [Group G]
namespace Kourovka.CentralLattice
theorem _root_.solution (u : G →* G)
    (k : Additive (Abelianization G) →ₗ[ℤ] Additive (Subgroup.center G)) :
    abelianMap (centralCorrection u (centralLift k)) = abelianMap u + centerImage.comp k := by
  ext a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
  change Abelianization.of (u x * ↑(centralLift k x)) =
    Abelianization.of (u x) * Abelianization.of (↑(centralLift k x) : G)
  exact map_mul Abelianization.of _ _
end Kourovka.CentralLattice
