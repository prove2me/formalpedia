-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_laurent_single
-- name    : Kourovka.MetabelianEnumeration.CommutatorModule.laurent_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:35.358641+00:00
-- url     : https://prove2.me/theorems/5cdbf107-8ae9-4b60-a1cf-7808b36bb6cf
-- title:
--   Commutator Module: laurent single
-- statement:
--   The Commutator Module construction uses the laurent single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/LaurentAction.lean#L26-L37
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/LaurentAction.lean#L26-L37

import Definitions.Def_Kourovka_Modules_CommutatorModule
import Definitions.Def_Kourovka_Modules_LaurentAction
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {E Q L : Type} [Group E] [CommGroup Q] [AddCommGroup L]
variable (π : E →* Q) (hπ : Function.Surjective π) [IsMulCommutative π.ker]
variable (q : Multiplicative L →* Q)

theorem Kourovka.MetabelianEnumeration.CommutatorModule.laurent_single (u : L) (a : Additive π.ker) :
    letI := laurentModule π hπ q
    (((AddMonoidAlgebra.single u 1 : AddMonoidAlgebra ℤ L) • a) : Additive π.ker).toMul =
      rightConjugation π hπ (q (Multiplicative.ofAdd u)) a.toMul := by sorry
