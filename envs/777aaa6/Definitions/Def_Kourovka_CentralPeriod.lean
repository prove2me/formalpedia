-- Prove2me | Definitions.Def_Kourovka_CentralPeriod
-- name    : Kourovka_CentralPeriod
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:28:38.906195+00:00
-- url     : https://prove2.me/theorems/3dfdc473-cbee-4812-b46c-367ac40d3bf0
-- title:
--   Central Period
-- statement:
--   Definitions and structural lemmas for Central Period, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralPeriod.lean

import Definitions.Def_Kourovka_AbelianWeight
import Definitions.Def_Kourovka_FinitePaths
set_option autoImplicit true
namespace Kourovka.CentralPeriod
variable (M : Type*) [AddCommGroup M]
def multiples (d : ℤ) : Submodule ℤ M :=
  LinearMap.range (d • (LinearMap.id : M →ₗ[ℤ] M))
def quotientMap (f : M →ₗ[ℤ] M) (d : ℤ) :
    M ⧸ multiples M d →ₗ[ℤ] M ⧸ multiples M d :=
  (multiples M d).mapQ (multiples M d) f (by
    rintro x ⟨y, rfl⟩
    exact ⟨f y, (f.map_smul d y).symm⟩)
end Kourovka.CentralPeriod


