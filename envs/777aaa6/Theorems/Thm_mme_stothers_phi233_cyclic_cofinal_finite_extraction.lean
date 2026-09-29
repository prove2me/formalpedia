-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_cofinal_finite_extraction
-- name    : mme_stothers_phi233_cyclic_cofinal_finite_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:18:23.605709+00:00
-- url     : https://prove2.me/theorems/df643e35-4085-4755-9de5-e4597df739d4
-- title:
--   Davie–Stothers phi_233: source-faithful cofinal finite extraction
-- statement:
--   Let $K$ be a field, let $2\le 3\tau\le3$, and fix a nonnegative base $V$ strictly below the Davie–Stothers value
--
--   $$
--   R_{233}=\frac{4(E+L)^2(2H+L)}{L}.
--   $$
--
--   Then there are tensor powers $s(n)\to\infty$ and a real loss $\ell(n)\to0$ such that, eventually, the $s(n)$-th power of the cyclic symmetrization of the literal constituent $\varphi_{233}$ restricts to a finite direct sum of matrix-multiplication tensors whose $\tau$-weighted volume is at least
--
--   $$
--   V^{s(n)}(1-\ell(n)).
--   $$
--
--   This is the exact finite-extraction form of Lemma 5.1(v). It keeps the retained direct sum and the vanishing loss explicit, so the remaining work consists precisely of the five-valued affine hashing, same-marginal completion ratio, component tensor values, and subexponential-loss assembly.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v), printed pp. 366--367, including the exceptional T_{233} hashing and same-marginal count; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. See also A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 25.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_cofinal_finite_extraction
    {K : Type u} [Field K] (tau : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < MME.StothersFourth.classValue 6 tau 9) :
    ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto loss atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
            ((cyclicSymmetrization
              (MME.StothersFourth.cwFourthConstituent K 6 2 3 3)).kronPow
                (s n)) ∧
          V ^ (s n) * (1 - loss n) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  sorry
