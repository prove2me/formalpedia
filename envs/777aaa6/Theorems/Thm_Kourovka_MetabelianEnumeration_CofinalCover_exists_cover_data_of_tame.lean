-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_exists_cover_data_of_tame
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.exists_cover_data_of_tame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:13:51.976504+00:00
-- url     : https://prove2.me/theorems/7e12bc98-7cf1-4c16-acdc-13f3fb5acab2
-- title:
--   Cofinal Cover: exists cover data of tame
-- statement:
--   A tame actual Laurent action produces finite cover data, including an
--   identity kernel generator so the kernel alphabet is always nonempty. The
--   same realization works at every radius.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalRealization.lean#L120-L157
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalRealization.lean#L120-L157

import Definitions.Def_Kourovka_Cofinality_LatticePullback
import Definitions.Def_Kourovka_Modules_ModuleRealization
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Modules_FiniteModuleGenerators
import Definitions.Def_Kourovka_Cofinality_CofinalRealization
set_option autoImplicit true
noncomputable section
set_option maxHeartbeats 50000
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
open FiniteCover CommutatorModule ModuleRealization ValuationModule SignedTameness
open TamenessCompactness
variable {k : ℕ} {E : Type} [Group E]
variable (π : E →* Multiplicative (Lattice k))
variable [IsMulCommutative π.ker]
variable [Module (GroupRing (Lattice k)) (Additive π.ker)]

theorem Kourovka.MetabelianEnumeration.CofinalCover.exists_cover_data_of_tame (t : Fin k → E)
    (ht : ∀ i, π (t i) = Multiplicative.ofAdd (Pi.single i 1))
    (hact : ActionCompatible (kernelInclusion π) t)
    [Module.Finite (GroupRing (Lattice k)) (Additive π.ker)]
    (htame : Tame (k := k) (Additive π.ker)) :
    ∃ a : ℕ, 1 ≤ a ∧ ∃ data : Datum k a,
      ConeVerifier.ConeCover (data.polynomials.map polynomialSupport) ∧
      ∀ radius : ℕ, ∃ f : FiniteCover.GroupOf data radius →* E, Function.Surjective f := by sorry
