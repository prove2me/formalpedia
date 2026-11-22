-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_exists_tame_cover_data
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.exists_tame_cover_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:13:48.65772+00:00
-- url     : https://prove2.me/theorems/48392a06-89e3-47af-98ee-33eca0157d17
-- title:
--   Cofinal Cover: exists tame cover data
-- statement:
--   The Cofinal Cover construction uses the exists tame cover data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalRealization.lean#L161-L173
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalRealization.lean#L161-L173

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

theorem Kourovka.MetabelianEnumeration.CofinalCover.exists_tame_cover_data (hπ : Function.Surjective π) :
    letI := laurentModule π hπ (MonoidHom.id (Multiplicative (Lattice k)))
    Module.Finite (GroupRing (Lattice k)) (Additive π.ker) →
    Tame (k := k) (Additive π.ker) →
    ∃ a : ℕ, 1 ≤ a ∧ ∃ data : Datum k a,
      ConeVerifier.ConeCover (data.polynomials.map polynomialSupport) ∧
      ∀ radius : ℕ, ∃ f : FiniteCover.GroupOf data radius →* E, Function.Surjective f := by sorry
