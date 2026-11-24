-- Prove2me | Theorems.Thm_sum_quadraticChar_sub
-- name    : sum_quadraticChar_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:33.092527+00:00
-- url     : https://prove2.me/theorems/15bc2e37-e5b6-4c81-89be-9c8ba99a056a
-- title:
--   sum quadratic Char sub: sum quadratic Char sub
-- statement:
--   The quadratic character sums to zero over any translate of `F`.
--   (Section 2 of `bs_lambda.txt`.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L46-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L46-L49

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

theorem sum_quadraticChar_sub (hF : ringChar F ≠ 2) (a : F) :
    ∑ z : F, quadraticChar F (z - a) = 0 := by sorry
