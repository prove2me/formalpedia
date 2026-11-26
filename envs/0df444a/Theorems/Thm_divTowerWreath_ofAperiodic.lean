-- Prove2me | Theorems.Thm_divTowerWreath_ofAperiodic
-- name    : divTowerWreath_ofAperiodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:27.846467+00:00
-- url     : https://prove2.me/theorems/83dffde8-39c6-59dd-9796-50081d35f414
-- title:
--   div Tower Wreath of Aperiodic: div Tower Wreath of Aperiodic
-- statement:
--   **Single aperiodic factor tower.**  A finite aperiodic monoid `M` has the
--       one-element factor tower `[KRFactor.ofAperiodic M hAper]`.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L179-L182
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L179-L182

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

theorem divTowerWreath_ofAperiodic (M : Type u) [Monoid M] [Finite M]
    (hAper : ∀ a : M, IsAperiodicElem a) :
    DivTowerWreath M [KRFactor.ofAperiodic M hAper] := by sorry
