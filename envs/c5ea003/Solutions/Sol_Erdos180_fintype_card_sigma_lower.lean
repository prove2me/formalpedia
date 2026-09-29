-- Prove2me | solution 1 for Erdos180.fintype_card_sigma_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:52:44.149757+00:00
-- url     : https://prove2.me/submissions/12e755e2-b27c-4664-be10-133c45f02063

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

open Erdos180
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem solution
    {α : Type*} [Fintype α]
    {β : α → Type*} [∀ a, Fintype (β a)]
    {baseLower fiberLower : ℕ}
    (hbase : baseLower ≤ Fintype.card α)
    (hfiber : ∀ a : α, fiberLower ≤ Fintype.card (β a)) :
    baseLower * fiberLower ≤ Fintype.card (Sigma β) := by
  classical
  rw [Fintype.card_sigma]
  calc
    baseLower * fiberLower ≤ Fintype.card α * fiberLower :=
      Nat.mul_le_mul_right fiberLower hbase
    _ = ∑ _a : α, fiberLower := by simp
    _ ≤ ∑ a : α, Fintype.card (β a) :=
      Finset.sum_le_sum fun a _ => hfiber a
