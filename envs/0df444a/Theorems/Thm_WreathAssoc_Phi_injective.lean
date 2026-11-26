-- Prove2me | Theorems.Thm_WreathAssoc_Phi_injective
-- name    : WreathAssoc.Phi_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:59.469193+00:00
-- url     : https://prove2.me/theorems/4ed10a4d-1322-487b-847c-58a42e89041f
-- title:
--   Wreath Assoc: Phi injective
-- statement:
--   The Wreath Assoc construction uses the Phi injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L278-L286
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L278-L286

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
open WreathAssoc
variable (G B' B Y X : Type u) [Monoid G] [Monoid B'] [Monoid B]
  [MulAction B' Y] [MulAction B X]
attribute [local instance] actW

theorem WreathAssoc.Phi_injective : Function.Injective (Phi G B' B Y X) := by sorry
