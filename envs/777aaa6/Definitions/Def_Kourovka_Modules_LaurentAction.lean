-- Prove2me | Definitions.Def_Kourovka_Modules_LaurentAction
-- name    : Kourovka_Modules_LaurentAction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:44:49.51132+00:00
-- url     : https://prove2.me/theorems/272fa8f5-f789-401b-b5de-365e06aec944
-- title:
--   Laurent Action
-- statement:
--   Definitions and structural lemmas for Laurent Action, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/LaurentAction.lean

import Definitions.Def_Kourovka_Modules_CommutatorModule
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.CommutatorModule
variable {E Q L : Type} [Group E] [CommGroup Q] [AddCommGroup L]
variable (π : E →* Q) (hπ : Function.Surjective π) [IsMulCommutative π.ker]
variable (q : Multiplicative L →* Q)
noncomputable def laurentModule : Module (AddMonoidAlgebra ℤ L) (Additive π.ker) :=
  Module.compHom (Additive π.ker)
    ((Representation.asAlgebraHom ((rightRepresentation π hπ).comp q)).toRingHom.comp
      (AddMonoidAlgebra.toMultiplicative ℤ L).toRingHom)
end Kourovka.MetabelianEnumeration.CommutatorModule


