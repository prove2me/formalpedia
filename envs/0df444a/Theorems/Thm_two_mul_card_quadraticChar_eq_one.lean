-- Prove2me | Theorems.Thm_two_mul_card_quadraticChar_eq_one
-- name    : two_mul_card_quadraticChar_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:33.380845+00:00
-- url     : https://prove2.me/theorems/a236cf0f-e337-4a34-bba8-fdaf19d25efb
-- title:
--   two mul card quadratic Char eq one: two mul card quadratic Char eq one
-- statement:
--   Exactly half of the nonzero elements of `F` are quadratic residues; this gives the out-degree
--   `(k - 1) / 2` of the Paley tournament. (Section 2 of `bs_lambda.txt`.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L107-L119
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L107-L119

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

theorem two_mul_card_quadraticChar_eq_one (hF : ringChar F ≠ 2) :
    2 * (univ.filter fun a : F ↦ quadraticChar F a = 1).card + 1 = Fintype.card F := by sorry
