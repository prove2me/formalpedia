-- Prove2me | Theorems.Thm_mme_stothers_phi125_cyclic_cofinal_finite_extraction
-- name    : mme_stothers_phi125_cyclic_cofinal_finite_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:39:28.871838+00:00
-- url     : https://prove2.me/theorems/bf2ea39d-c52d-4aa9-a63f-93c0478003be
-- title:
--   Davie–Stothers $\varphi_{125}$: cofinal finite extraction
-- statement:
--   Let $K$ be a field and let $2\le 3\tau\le3$. Fix a nonnegative base $V$ strictly below the Davie–Stothers endpoint $$R_{125}=\frac{4(L+EH)(2H+L)}{H}.$$ Then there are powers $s(n)\to\infty$ and losses $\ell(n)\to0$ such that, eventually, the $s(n)$-th power of the cyclic symmetrization of the literal constituent $\varphi_{125}$ restricts to a finite direct sum of matrix-multiplication tensors whose $\tau$-weighted volume is at least $$V^{s(n)}(1-\ell(n)).$$ This is the source-faithful finite-extraction form of Lemma 5.1(ii). It retains the exact tensor restriction and makes the subexponential Salem–Spencer loss explicit; the already proved closure bridge then yields the downward-closed tau-value statement.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 5.1(ii), printed pp. 364–365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. See also A. J. Stothers, On the Complexity of Matrix Multiplication, PhD thesis, 2010, Chapter 4.3, Lemma 22.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_stothers_phi125_cyclic_cofinal_finite_extraction
    {K : Type u} [Field K] (tau : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < MME.StothersFourth.classValue 6 tau 6) :
    ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto loss atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
            ((cyclicSymmetrization
              (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)).kronPow
                (s n)) ∧
          V ^ (s n) * (1 - loss n) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  sorry
