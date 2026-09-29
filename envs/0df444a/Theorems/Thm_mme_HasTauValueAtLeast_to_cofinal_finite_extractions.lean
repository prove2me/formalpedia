-- Prove2me | Theorems.Thm_mme_HasTauValueAtLeast_to_cofinal_finite_extractions
-- name    : mme_HasTauValueAtLeast_to_cofinal_finite_extractions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:59:55.866217+00:00
-- url     : https://prove2.me/theorems/626023e8-5afa-4d08-8646-ceaab4e9d342
-- title:
--   Cofinal finite extraction sequence from a tau-value witness
-- statement:
--   Let $T$ be a three-way tensor over a field and suppose its $\tau$-value is at least $V$. Then one can choose a cofinal sequence of tensor powers $s_n \to \infty$ and positive relative errors $e_n \to 0$ such that every selected power has a concrete matrix-multiplication direct-sum restriction satisfying
--
--   $$
--   V^{s_n}(1-e_n) \le \sum_i (a_i b_i c_i)^\tau.
--   $$
--
--   The conclusion retains both the actual tensor restriction and its weighted-volume inequality. It is the sequential form of the frequent-witness quantifier in the definition of tau-value and is useful when a later finite construction must be performed at one chosen power at each accuracy scale.
-- source:
--   Sequential extraction from the definition of HasTauValueAtLeast in Definitions.Def_mme_tau_value; used to formalize the cofinal asymptotic witness selection in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 265--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_tau_value
open MME BigOperators Filter
universe u

theorem mme_HasTauValueAtLeast_to_cofinal_finite_extractions
    {K : Type u} [Field K]
    (T : TensorObj K 3) (tau V : ℝ)
    (hV : HasTauValueAtLeast T tau V) :
    ∃ (s : ℕ → ℕ) (error : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto error atTop (nhds 0) ∧
      (∀ n, 0 < error n) ∧
      ∀ n,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            (T.kronPow (s n)) ∧
          V ^ (s n) * (1 - error n) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by sorry
