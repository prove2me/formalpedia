-- Prove2me | Theorems.Thm_mme_HasTauValueAtLeast_exists_positive_extraction_below
-- name    : mme_HasTauValueAtLeast_exists_positive_extraction_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:44:38.454579+00:00
-- url     : https://prove2.me/theorems/311de337-60db-483a-bc69-f05f0670866e
-- title:
--   A strict tau-value target has a positive-power extraction
-- statement:
--   Let a tensor have tau-value at least a positive base `B`. For every nonnegative strict target `V<B`, there is a positive integer exponent `e` and a genuine finite restriction of the `e`-th tensor power to a direct sum of matrix-multiplication tensors whose total tau-weight is at least `V^e`. This removes the relative-error factor at one positive exponent and supplies the slack needed for common-power synchronization.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.4 and the strict component-value use in Section 6.3 and Equation (25), PDF pp. 13 and 59-60; https://arxiv.org/abs/2210.10173. The lemma is the cofinal-exponent slack extraction implicit in asymptotic tensor value arguments.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Definitions.Def_mme_tau_value

open Filter BigOperators
open MME

set_option autoImplicit false

universe u

theorem mme_HasTauValueAtLeast_exists_positive_extraction_below
    {K : Type u} [Field K]
    (T : TensorObj K 3) (tau B V : ℝ)
    (hB : 0 < B) (hV : 0 ≤ V) (hVB : V < B)
    (h : HasTauValueAtLeast T tau B) :
    ∃ e : ℕ, 0 < e ∧
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
          (T.kronPow e) ∧
        V ^ e ≤ ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by sorry
