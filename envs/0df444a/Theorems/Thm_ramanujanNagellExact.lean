-- Prove2me | Theorems.Thm_ramanujanNagellExact
-- name    : ramanujanNagellExact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:17.269698+00:00
-- url     : https://prove2.me/theorems/1c6e1974-c2c5-4137-bd11-ab05171e63b4
-- title:
--   ramanujan Nagell Exact: ramanujan Nagell Exact
-- statement:
--   Exact iff form of the Ramanujan-Nagell theorem: the integer solutions of
--       `x ^ 2 + 7 = 2 ^ n` are precisely `(±1, 3)`, `(±3, 4)`,
--       `(±5, 5)`, `(±11, 7)`, and `(±181, 15)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RamanujanNagell/Basic.lean#L1125-L1137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RamanujanNagell/Basic.lean#L1125-L1137

module
public import Definitions.Def_LeanPool_RamanujanNagell_Helpers
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_RamanujanNagell_Basic
set_option autoImplicit true
@[expose] public section
public section
open RamanujanNagell

theorem ramanujanNagellExact :
  ∀ x : ℤ, ∀ n : ℕ, x ^ 2 + 7 = 2 ^ n ↔
    (x, n) = (1, 3) ∨ (x, n) = (-1, 3)
  ∨ (x, n) = (3, 4) ∨ (x, n) = (-3, 4)
  ∨ (x, n) = (5, 5) ∨ (x, n) = (-5, 5)
  ∨ (x, n) = (11, 7) ∨ (x, n) = (-11, 7)
  ∨ (x, n) = (181, 15) ∨ (x, n) = (-181, 15) := by sorry
