-- Prove2me | Theorems.Thm_sgDiv_wreath_of_subsingleton_decoration
-- name    : sgDiv_wreath_of_subsingleton_decoration
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:53.712381+00:00
-- url     : https://prove2.me/theorems/44f242c4-4ff8-4bb0-ae55-269506f94b70
-- title:
--   sg Div wreath of subsingleton decoration: sg Div wreath of subsingleton decoration
-- statement:
--   When the decoration factor `A` is a subsingleton, `A ≀_X B ≅ B`, so `A ≀_X B`
--       divides `B` (the projection onto the base is an isomorphism).
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L353-L365
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L353-L365

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

theorem sgDiv_wreath_of_subsingleton_decoration (A B X : Type u) [Monoid A]
    [Finite A] [Monoid B] [Finite B] [Fintype X] [MulAction B X] [Subsingleton A] :
    SgDiv (WreathProduct A B X) B := by sorry
