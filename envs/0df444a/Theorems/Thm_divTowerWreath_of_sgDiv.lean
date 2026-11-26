-- Prove2me | Theorems.Thm_divTowerWreath_of_sgDiv
-- name    : divTowerWreath_of_sgDiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:36.171353+00:00
-- url     : https://prove2.me/theorems/9bc2bbb0-3325-4428-8306-20e2a4bc6fe7
-- title:
--   div Tower Wreath of sg Div: div Tower Wreath of sg Div
-- statement:
--   **Division transfers the factor tower.**  If `SgDiv S T` and
--       `DivTowerWreath T factors`, then `DivTowerWreath S factors`.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L200-L215
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L200-L215

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

theorem divTowerWreath_of_sgDiv {S T : Type u} [Monoid S] [Finite S]
    [Monoid T] [Finite T] (h : SgDiv S T) :
    ∀ {factors : List KRFactor.{u}}, DivTowerWreath T factors →
      DivTowerWreath S factors := by sorry
