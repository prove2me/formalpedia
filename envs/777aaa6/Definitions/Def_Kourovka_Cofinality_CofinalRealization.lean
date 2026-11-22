-- Prove2me | Definitions.Def_Kourovka_Cofinality_CofinalRealization
-- name    : Kourovka_Cofinality_CofinalRealization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:12:51.33467+00:00
-- url     : https://prove2.me/theorems/8f659e51-8f9f-4808-b9da-f2c01b7d1d31
-- title:
--   Cofinal Realization
-- statement:
--   Definitions and structural lemmas for Cofinal Realization, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalRealization.lean

import Definitions.Def_Kourovka_Cofinality_LatticePullback
import Definitions.Def_Kourovka_Modules_ModuleRealization
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Modules_FiniteModuleGenerators
set_option autoImplicit true
noncomputable section
set_option maxHeartbeats 50000
set_option autoImplicit false
namespace Kourovka.MetabelianEnumeration.CofinalCover
open FiniteCover CommutatorModule ModuleRealization ValuationModule SignedTameness
open TamenessCompactness
variable {k : ℕ} {E : Type} [Group E]
variable (π : E →* Multiplicative (Lattice k))
def kernelInclusion : Multiplicative (Additive π.ker) →* E where
  toFun m := m.toAdd.toMul.val
  map_one' := rfl
  map_mul' _ _ := rfl
variable [IsMulCommutative π.ker]
section CompatibleAction
variable [Module (GroupRing (Lattice k)) (Additive π.ker)]
end CompatibleAction
end Kourovka.MetabelianEnumeration.CofinalCover


