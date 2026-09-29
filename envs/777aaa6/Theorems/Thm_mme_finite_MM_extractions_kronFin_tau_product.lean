-- Prove2me | Theorems.Thm_mme_finite_MM_extractions_kronFin_tau_product
-- name    : mme_finite_MM_extractions_kronFin_tau_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:57:05.947399+00:00
-- url     : https://prove2.me/theorems/0f7851ef-0dfc-4575-bf9a-68ab29b1084d
-- title:
--   Multiply heterogeneous finite MM extractions with exact tau bookkeeping
-- statement:
--   Consider a finite family of order-three tensors. Suppose each tensor genuinely restricts to a finite direct sum of matrix-multiplication tensors whose total tau-weight is at least a specified nonnegative local bound. Then the Kronecker product of the family genuinely restricts to one finite direct sum of matrix-multiplication tensors whose total tau-weight is at least the product of all local bounds. The statement permits heterogeneous numbers and shapes of local summands.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.4 and the fifteen-component product in Section 6.3 and Equation (25), PDF pp. 13 and 59-60; https://arxiv.org/abs/2210.10173. This theorem is the finite source-faithful product rule needed to assemble heterogeneous component extractions.

import Mathlib.Tactic
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators

set_option autoImplicit false

universe u

theorem mme_finite_MM_extractions_kronFin_tau_product
    {K : Type u} [Field K] {n : ℕ}
    (Y : Fin n → TensorObj K 3) (tau : ℝ) (lower : Fin n → ℝ)
    (hlower : ∀ i, 0 ≤ lower i)
    (hextract : ∀ i : Fin n,
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
          (Y i) ∧
        lower i ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) :
    ∃ (q : ℕ) (A B C : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (C j)))
        (TensorObj.kronFin n Y) ∧
      (∏ i, lower i) ≤
        ∑ j, (((A j * B j * C j : ℕ) : ℝ) ^ tau) := by sorry
