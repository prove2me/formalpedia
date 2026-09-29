-- Prove2me | Theorems.Thm_mme_bigAdd_MM_kronPow_flatten
-- name    : mme_bigAdd_MM_kronPow_flatten
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:43:38.547318+00:00
-- url     : https://prove2.me/theorems/bd7c78d4-7fcd-44a5-bdc4-64f1c45cb2ef
-- title:
--   Flatten a powered finite MM direct sum by words
-- statement:
--   Let a finite direct sum consist of matrix-multiplication tensors with shapes `(a_i,b_i,c_i)`. Its `r`-th Kronecker power is tensor-isomorphic to a finite direct sum indexed by length-`r` words. The summand for a word has three dimensions equal to the coordinatewise products of the selected dimensions along that word. This is the exact distributive flattening needed to replicate a finite tau-value extraction.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.4 and the tensor-product assembly used in Section 6.3 and Equation (25), PDF pp. 13 and 59-60; https://arxiv.org/abs/2210.10173. The finite word expansion is the distributive Kronecker-product identity underlying the asymptotic sum inequality.

import Mathlib.Tactic
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators

set_option autoImplicit false

universe u

theorem mme_bigAdd_MM_kronPow_flatten
    {K : Type u} [Field K]
    {k r : ℕ} (a b c : Fin k → ℕ) :
    ∃ (q : ℕ) (A B C : Fin q → ℕ),
      TensorObj.Isomorphic
        (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (C j)))
        ((TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i))).kronPow r) := by sorry
