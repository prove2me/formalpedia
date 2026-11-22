-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_laurent_finite_of_normal_generators
-- name    : Kourovka.MetabelianEnumeration.CommutatorModule.laurent_finite_of_normal_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:35.013267+00:00
-- url     : https://prove2.me/theorems/40a5661e-525e-46e2-accd-9168d4e2be0a
-- title:
--   Commutator Module: laurent finite of normal generators
-- statement:
--   Finite normal generators become finite generators for the concrete
--   Laurent action.  Surjectivity of the quotient map supplies every conjugation
--   as a monomial action.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/LaurentAction.lean#L51-L93
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/LaurentAction.lean#L51-L93

import Definitions.Def_Kourovka_Modules_CommutatorModule
import Definitions.Def_Kourovka_Modules_LaurentAction
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {E Q L : Type} [Group E] [CommGroup Q] [AddCommGroup L]
variable (π : E →* Q) (hπ : Function.Surjective π) [IsMulCommutative π.ker]
variable (q : Multiplicative L →* Q)

theorem Kourovka.MetabelianEnumeration.CommutatorModule.laurent_finite_of_normal_generators (hq : Function.Surjective q)
    (s : Finset π.ker)
    (hs : Subgroup.normalClosure (Subtype.val '' (s : Set π.ker)) = π.ker) :
    letI := laurentModule π hπ q
    Module.Finite (AddMonoidAlgebra ℤ L) (Additive π.ker) := by sorry
