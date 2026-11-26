-- Prove2me | Theorems.Thm_divTowerWreath_nil_of_subsingleton
-- name    : divTowerWreath_nil_of_subsingleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:34.651802+00:00
-- url     : https://prove2.me/theorems/847308be-de2f-46cd-870c-7af560d732f9
-- title:
--   div Tower Wreath nil of subsingleton: div Tower Wreath nil of subsingleton
-- statement:
--   The empty factor tower for a subsingleton monoid: a subsingleton `M`
--       divides `PUnit`.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L157-L164
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L157-L164

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

theorem divTowerWreath_nil_of_subsingleton (M : Type u) [Monoid M] [Finite M]
    [Subsingleton M] : DivTowerWreath M ([] : List KRFactor.{u}) := by sorry
