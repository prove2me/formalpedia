-- Prove2me | Theorems.Thm_sgDiv_wreath_assoc
-- name    : sgDiv_wreath_assoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:39.041348+00:00
-- url     : https://prove2.me/theorems/d3c5e97d-8cd1-4f80-b80b-b1b7973a94ec
-- title:
--   sg Div wreath assoc: sg Div wreath assoc
-- statement:
--   **Wreath associativity, up to division.**  `(G ≀_Y B') ≀_X B` divides
--       `G ≀_{Y × X} W`, where the base `W = B' ≀_X B` acts on `Y × X` by
--       `WreathAssoc.actW` (the inner base on the inner state, the outer base on the
--       outer state).  Fully proved via the unscrambling embedding `WreathAssoc.Phi`
--       (an injective semigroup homomorphism).
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L295-L304
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L295-L304

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

theorem sgDiv_wreath_assoc (G B' B Y X : Type u)
    [Monoid G] [Finite G] [Monoid B'] [Finite B']
    [Monoid B] [Finite B] [Fintype Y] [Fintype X]
    [MulAction B' Y] [MulAction B X] :
    letI := WreathAssoc.actW B' B Y X
    SgDiv (WreathProduct (WreathProduct G B' Y) B X)
          (WreathProduct G (WreathProduct B' B X) (Y × X)) := by sorry
