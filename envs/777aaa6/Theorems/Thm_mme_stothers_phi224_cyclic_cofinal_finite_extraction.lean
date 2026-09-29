-- Prove2me | Theorems.Thm_mme_stothers_phi224_cyclic_cofinal_finite_extraction
-- name    : mme_stothers_phi224_cyclic_cofinal_finite_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:05:08.739045+00:00
-- url     : https://prove2.me/theorems/e1ef1940-a204-46de-98e1-d5fe864cf9ed
-- title:
--   Davie–Stothers phi_224: source-faithful cofinal finite extraction
-- statement:
--   Let $K$ be a field, let $2\le 3\tau\le3$, and fix a nonnegative base $V$ strictly below the Davie–Stothers value
--
--   $$
--   R_{224}=\frac{(2H+L)^2(2+2E+H)}{H}.
--   $$
--
--   Then there are tensor powers $s(n)\to\infty$ and real losses $\ell(n)\to0$ such that, eventually, the $s(n)$-th power of the cyclic symmetrization of the literal constituent $\varphi_{224}$ restricts to a finite direct sum of matrix-multiplication tensors whose $\tau$-weighted volume is at least
--
--   $$
--   V^{s(n)}(1-\ell(n)).
--   $$
--
--   This is the finite-extraction form of Lemma 5.1(iv). It keeps the literal nine-component type-2 profile, progression-free hashing, and subexponential loss visible, while avoiding an unjustified claim at the limiting endpoint itself.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(iv), printed pp. 365–366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf. See also A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 24.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_stothers_phi224_cyclic_cofinal_finite_extraction
    {K : Type u} [Field K] (tau : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < MME.StothersFourth.classValue 6 tau 8) :
    ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto loss atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
            ((cyclicSymmetrization
              (MME.StothersFourth.cwFourthConstituent K 6 2 2 4)).kronPow
                (s n)) ∧
          V ^ (s n) * (1 - loss n) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  sorry
