-- Prove2me | Theorems.Thm_sgDiv_wreath_decoration_mono
-- name    : sgDiv_wreath_decoration_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:34.759564+00:00
-- url     : https://prove2.me/theorems/f08d7668-1735-47c4-a74d-b6d66137bf72
-- title:
--   sg Div wreath decoration mono: sg Div wreath decoration mono
-- statement:
--   **Wreath product is monotone in the decoration factor.**  If `A` divides
--       `A'`, then `A ≀_X B` divides `A' ≀_X B`: lift the surjection
--       `U' ↠ A` pointwise over the decoration, restricting to the subsemigroup of
--       `A' ≀_X B` whose decorations land in `U'`.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L310-L336
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L310-L336

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

theorem sgDiv_wreath_decoration_mono (A A' B X : Type u) [Monoid A] [Finite A]
    [Monoid A'] [Finite A'] [Monoid B] [Finite B] [Fintype X] [MulAction B X]
    (h : SgDiv A A') :
    SgDiv (WreathProduct A B X) (WreathProduct A' B X) := by sorry
