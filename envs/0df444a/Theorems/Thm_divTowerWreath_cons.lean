-- Prove2me | Theorems.Thm_divTowerWreath_cons
-- name    : divTowerWreath_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:57.9957+00:00
-- url     : https://prove2.me/theorems/0b29b9ea-78b8-5e6f-afde-31bef4b82129
-- title:
--   div Tower Wreath cons: div Tower Wreath cons
-- statement:
--   The div Tower Wreath cons construction uses the div Tower Wreath cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L119-L125
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L119-L125

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

theorem divTowerWreath_cons (M : Type u) [Monoid M] [Finite M]
    (F : KRFactor.{u}) (rest : List KRFactor.{u}) :
    DivTowerWreath M (F :: rest) ↔
      ∃ (B : Type u) (_ : Monoid B) (_ : Finite B)
        (Y : Type u) (_ : Fintype Y) (_ : MulAction B Y),
        DivTowerWreath B rest ∧
        SgDiv M (WreathProduct F.carrier B Y) := by sorry
