-- Prove2me | Theorems.Thm_four_mul_card_quadraticChar_sub_eq_one
-- name    : four_mul_card_quadraticChar_sub_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:40.72048+00:00
-- url     : https://prove2.me/theorems/a432edb3-3802-479e-ab75-a6b345e4f9e7
-- title:
--   four mul card quadratic Char sub eq one: four mul card quadratic Char sub eq one
-- statement:
--   For `a ≠ b`, exactly `(#F - 3) / 4` elements `z` satisfy `χ (z - a) = χ (z - b) = 1`.
--   This is the common-out-neighbour count of the Paley tournament.
--   (Section 2 of `bs_lambda.txt`.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L177-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L177-L192

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
set_option autoImplicit true
@[expose] public section
public section
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem four_mul_card_quadraticChar_sub_eq_one (hF : ringChar F ≠ 2)
    (hneg : quadraticChar F (-1) = -1) {a b : F} (hab : a ≠ b) :
    4 * (univ.filter fun z : F ↦
        quadraticChar F (z - a) = 1 ∧ quadraticChar F (z - b) = 1).card + 3
      = Fintype.card F := by sorry
