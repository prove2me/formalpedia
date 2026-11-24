-- Prove2me | Theorems.Thm_sum_quadraticChar_mul_sub
-- name    : sum_quadraticChar_mul_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:30.575078+00:00
-- url     : https://prove2.me/theorems/e99e2f66-d7de-4da3-9230-e39d78cf11a7
-- title:
--   sum quadratic Char mul sub: sum quadratic Char mul sub
-- statement:
--   The Jacobsthal-type identity `∑ z, χ ((z - a) * (z - b)) = -1` for `a ≠ b`.
--   This is the key identity of the character-sum calculation in Section 2 of `bs_lambda.txt`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L53-L103
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L53-L103

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

theorem sum_quadraticChar_mul_sub (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ z : F, quadraticChar F ((z - a) * (z - b)) = -1 := by sorry
