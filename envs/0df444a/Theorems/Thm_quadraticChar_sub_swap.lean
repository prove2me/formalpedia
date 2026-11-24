-- Prove2me | Theorems.Thm_quadraticChar_sub_swap
-- name    : quadraticChar_sub_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:35.718483+00:00
-- url     : https://prove2.me/theorems/e4e92313-b571-44d8-8d6e-cf6ac2779335
-- title:
--   quadratic Char sub swap: quadratic Char sub swap
-- statement:
--   When `-1` is a nonresidue, swapping the two arguments of a difference negates the quadratic
--   character. (Section 2 of `bs_lambda.txt`.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L123-L125
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L123-L125

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

theorem quadraticChar_sub_swap (hneg : quadraticChar F (-1) = -1) (a b : F) :
    quadraticChar F (a - b) = -quadraticChar F (b - a) := by sorry
