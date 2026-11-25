-- Prove2me | Theorems.Thm_sub_le_sum_Ico_inv_sq
-- name    : sub_le_sum_Ico_inv_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:27:34.58095+00:00
-- url     : https://prove2.me/theorems/2ef7489b-c166-417e-8211-65b0f3a9d493
-- title:
--   sub le sum Ico inv sq: sub le sum Ico inv sq
-- statement:
--   The lower bound matching `sum_Ioc_inv_sq_le_sub`:
--   `1 / k - 1 / n ≤ ∑_{k ≤ i < n} 1 / i ^ 2`.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/DeBruijnErdos.lean#L65-L75
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/DeBruijnErdos.lean#L65-L75

module
public import Definitions.Def_Fekete_Window
public import Mathlib.Analysis.PSeries
public import Definitions.Def_Fekete_DeBruijnErdos
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Finset
open scoped Topology
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem sub_le_sum_Ico_inv_sq {k n : ℕ} (hk : k ≠ 0) (h : k ≤ n) :
    (k : α)⁻¹ - (n : α)⁻¹ ≤ ∑ i ∈ Ico k n, ((i : α) ^ 2)⁻¹ := by sorry
