-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_laurent_single_image
-- name    : Kourovka.MetabelianEnumeration.CommutatorModule.laurent_single_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:51.026613+00:00
-- url     : https://prove2.me/theorems/8d14b879-d77a-4d45-9f64-c45235986a56
-- title:
--   Commutator Module: laurent single image
-- statement:
--   The Commutator Module construction uses the laurent single image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/LaurentAction.lean#L39-L46
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/LaurentAction.lean#L39-L46

import Definitions.Def_Kourovka_Modules_CommutatorModule
import Definitions.Def_Kourovka_Modules_LaurentAction
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {E Q L : Type} [Group E] [CommGroup Q] [AddCommGroup L]
variable (π : E →* Q) (hπ : Function.Surjective π) [IsMulCommutative π.ker]
variable (q : Multiplicative L →* Q)

theorem Kourovka.MetabelianEnumeration.CommutatorModule.laurent_single_image (u : L) (g : E)
    (hu : q (Multiplicative.ofAdd u) = π g) (a : Additive π.ker) :
    letI := laurentModule π hπ q
    (((AddMonoidAlgebra.single u 1 : AddMonoidAlgebra ℤ L) • a) : Additive π.ker).toMul.val =
      g⁻¹ * a.toMul.val * g := by sorry
