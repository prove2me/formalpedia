-- Prove2me | Theorems.Thm_sgDiv_wreath_subsingleton_base
-- name    : sgDiv_wreath_subsingleton_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:07.52286+00:00
-- url     : https://prove2.me/theorems/6c876244-ef1c-4f60-8b4e-883523cdb014
-- title:
--   sg Div wreath subsingleton base: sg Div wreath subsingleton base
-- statement:
--   A monoid `A` over a *subsingleton* base `B` divides `A ≀_B B`
--       (the wreath of `A` over the trivial base, with `B` acting on itself).  This
--       is the "one rung" building block: when `B` is a single point the wreath
--       multiplication collapses to a copy of `A`.
--
--       Stated for a general subsingleton `B` (rather than literally `PUnit`) so that
--       the wreath-product instances match exactly those produced by the cons case of
--       `DivTowerWreath` at the call site (avoiding `MulAction PUnit PUnit` instance
--       ambiguity).
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L138-L153
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L138-L153

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

theorem sgDiv_wreath_subsingleton_base (A B : Type u) [Monoid A] [Monoid B]
    [Subsingleton B] :
    SgDiv A (WreathProduct A B B) := by sorry
