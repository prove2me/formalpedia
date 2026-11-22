-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_laurent_action_compatible
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.laurent_action_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:13:42.218204+00:00
-- url     : https://prove2.me/theorems/844ab1b4-56eb-4543-a6c4-f006dd9ebe6e
-- title:
--   Cofinal Cover: laurent action compatible
-- statement:
--   The Cofinal Cover construction uses the laurent action compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalRealization.lean#L59-L66
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalRealization.lean#L59-L66

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

theorem Kourovka.MetabelianEnumeration.CofinalCover.laurent_action_compatible (hπ : Function.Surjective π) (t : Fin k → E)
    (ht : ∀ i, π (t i) = Multiplicative.ofAdd (Pi.single i 1)) :
    letI := laurentModule π hπ (MonoidHom.id (Multiplicative (Lattice k)))
    ActionCompatible (kernelInclusion π) t := by sorry
