-- Prove2me | Theorems.Thm_divTowerWreath_single
-- name    : divTowerWreath_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:05.309311+00:00
-- url     : https://prove2.me/theorems/92f28e34-5cc4-524a-b366-be356d4699cf
-- title:
--   div Tower Wreath single: div Tower Wreath single
-- statement:
--   A single-factor tower over a factor `F`: `DivTowerWreath F.carrier [F]`,
--       witnessed by the `PUnit` base.  (Stated directly over `F.carrier` with its
--       canonical `F.mon`/`F.fin` instances so the wreath-product instances coincide
--       with the recursive predicate's.)
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L170-L175
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L170-L175

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_Cayley
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_FactorTower
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.unusedSectionVars false
universe u
open Green

theorem divTowerWreath_single (F : KRFactor.{u}) :
    DivTowerWreath F.carrier [F] := by sorry
