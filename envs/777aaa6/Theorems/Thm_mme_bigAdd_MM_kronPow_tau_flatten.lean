-- Prove2me | Theorems.Thm_mme_bigAdd_MM_kronPow_tau_flatten
-- name    : mme_bigAdd_MM_kronPow_tau_flatten
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:47:19.219283+00:00
-- url     : https://prove2.me/theorems/6b5061e0-c5d6-47d9-89f2-dc1bbe77525b
-- title:
--   Lossless tau-weighted replication of a finite MM extraction
-- statement:
--   For any finite direct sum of matrix-multiplication tensors, any nonnegative integer replication count `r`, and any real `tau`, the `r`-th Kronecker power restricts to a finite direct sum of matrix-multiplication tensors whose total tau-weight is exactly the `r`-th power of the original total tau-weight. The theorem retains the literal tensor restriction as well as the exact weighted-volume identity.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.4 and the product assembly in Section 6.3 and Equation (25), PDF pp. 13 and 59-60; https://arxiv.org/abs/2210.10173. This is the exact finite replication lemma underlying common-power asymptotic value assembly.

import Mathlib.Tactic
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_MM_word_tau_weight

open MME BigOperators

set_option autoImplicit false

universe u

theorem mme_bigAdd_MM_kronPow_tau_flatten
    {K : Type u} [Field K]
    {k r : ℕ} (a b c : Fin k → ℕ) (tau : ℝ) :
    ∃ (q : ℕ) (A B C : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (C j)))
        ((TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i))).kronPow r) ∧
      (∑ j, (((A j * B j * C j : ℕ) : ℝ) ^ tau)) =
        (∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) ^ r := by sorry
