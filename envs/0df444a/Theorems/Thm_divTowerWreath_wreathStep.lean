-- Prove2me | Theorems.Thm_divTowerWreath_wreathStep
-- name    : divTowerWreath_wreathStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:18.756894+00:00
-- url     : https://prove2.me/theorems/8fb737b5-01c3-43f4-a0f7-c8257494a406
-- title:
--   div Tower Wreath wreath Step: div Tower Wreath wreath Step
-- statement:
--   **The factor-tower concatenation step.**
--
--       If `S` divides `A ≀_X B`, the decoration factor `A` has a factor tower
--       `towA`, and the base factor `B` has a factor tower `towB`, then `S` has the
--       *concatenated* factor tower `towA ++ towB`.
--
--       It flattens the two sub-decompositions into one explicit list.  The proof is by
--       induction on `towA`, using `sgDiv_wreath_decoration_mono` to push the
--       decomposition of `A` into the decoration slot and `sgDiv_wreath_assoc` to
--       re-associate the nested wreath into the base.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L377-L419
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L377-L419

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

theorem divTowerWreath_wreathStep :
    ∀ (towA : List KRFactor.{u}) {S A B X : Type u}
      [Monoid S] [Finite S] [Monoid A] [Finite A] [Monoid B] [Finite B]
      [Fintype X] [MulAction B X],
      SgDiv S (WreathProduct A B X) → DivTowerWreath A towA →
      ∀ {towB : List KRFactor.{u}}, DivTowerWreath B towB →
        DivTowerWreath S (towA ++ towB) := by sorry
