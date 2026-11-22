-- Prove2me | Definitions.Def_Kourovka_Cofinality_Cofinality
-- name    : Kourovka_Cofinality_Cofinality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:23:50.36599+00:00
-- url     : https://prove2.me/theorems/fe5b9f2f-9449-4335-9644-97feb9aac5b8
-- title:
--   Cofinality
-- statement:
--   Definitions and structural lemmas for Cofinality, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/Cofinality.lean

import Definitions.Def_Kourovka_Cofinality_CofinalRealization
import Definitions.Def_Kourovka_Halfspaces_BieriStrebelNecessity
set_option autoImplicit true
noncomputable section
set_option autoImplicit false
namespace Kourovka.MetabelianEnumeration.CofinalCover
open FiniteCover CommutatorModule ValuationModule SignedTameness
open TamenessCompactness
end Kourovka.MetabelianEnumeration.CofinalCover


