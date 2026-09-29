-- Prove2me | Theorems.Thm_mme_HasTauValueAtLeast_multiple_extractions_below
-- name    : mme_HasTauValueAtLeast_multiple_extractions_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:55:41.261979+00:00
-- url     : https://prove2.me/theorems/17604da3-2d7c-49fe-98f1-4386ecef43af
-- title:
--   Strict tau-value witnesses replicate on an integral power lattice
-- statement:
--   Let a tensor have tau-value at least a positive base `B`, and fix a nonnegative strict target `V<B`. There is a positive integer `e` such that, for every nonnegative integer `r`, the tensor power `T^(r e)` genuinely restricts to a finite direct sum of matrix-multiplication tensors with total tau-weight at least `V^(r e)`. Thus a strict asymptotic value witness can be replicated on a full cofinal integral lattice of exponents.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.4 and the divisible-power assembly implicit in Section 6.3 and Equation (25), PDF pp. 13 and 59-60; https://arxiv.org/abs/2210.10173. This is the explicit cofinal/integral exponent lemma required to synchronize strict component values.

import Mathlib.Tactic
import Theorems.Thm_mme_kronPow_kronPow_isomorphic
import Theorems.Thm_mme_restrict_kronPow
import Theorems.Thm_mme_bigAdd_MM_kronPow_tau_flatten
import Theorems.Thm_mme_HasTauValueAtLeast_exists_positive_extraction_below

open BigOperators
open MME

set_option autoImplicit false

universe u

theorem mme_HasTauValueAtLeast_multiple_extractions_below
    {K : Type u} [Field K]
    (T : TensorObj K 3) (tau B V : ℝ)
    (hB : 0 < B) (hV : 0 ≤ V) (hVB : V < B)
    (h : HasTauValueAtLeast T tau B) :
    ∃ e : ℕ, 0 < e ∧
      ∀ r : ℕ,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
            (T.kronPow (r * e)) ∧
          V ^ (r * e) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by sorry
