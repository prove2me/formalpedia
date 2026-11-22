-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_projection_orderedWord
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.projection_orderedWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:13:36.457955+00:00
-- url     : https://prove2.me/theorems/2c4b9cee-a271-4ef7-94c1-d1d06a19e68f
-- title:
--   Cofinal Cover: projection ordered Word
-- statement:
--   The Cofinal Cover construction uses the projection ordered Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalRealization.lean#L35-L43
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalRealization.lean#L35-L43

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

theorem Kourovka.MetabelianEnumeration.CofinalCover.projection_orderedWord (t : Fin k → E)
    (ht : ∀ i, π (t i) = Multiplicative.ofAdd (Pi.single i 1)) (v : Lattice k) :
    π (orderedWord t v) = Multiplicative.ofAdd v := by sorry
