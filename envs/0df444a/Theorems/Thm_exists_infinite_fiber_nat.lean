-- Prove2me | Theorems.Thm_exists_infinite_fiber_nat
-- name    : exists_infinite_fiber_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:46.423573+00:00
-- url     : https://prove2.me/theorems/8fdb287b-2c91-4bb3-a2c8-83be485e19dd
-- title:
--   exists infinite fiber nat: exists infinite fiber nat
-- statement:
--   **Infinite pigeonhole.** A sequence `f : ℕ → κ` with `κ` finite takes some value `k` on an
--   infinite set of indices.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Data/Fintype/Pigeonhole.lean#L31-L34
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Data/Fintype/Pigeonhole.lean#L31-L34

module
public import Aesop.BuiltinRules
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Definitions.Def_LeanPool_NashWilliams_Data_Fintype_Pigeonhole
set_option autoImplicit true
@[expose] public section
public section

theorem exists_infinite_fiber_nat {κ : Type*} [Finite κ] (f : ℕ → κ) :
    ∃ k : κ, {n : ℕ | f n = k}.Infinite := by sorry
