-- Prove2me | Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions
-- name    : mme_HasTauValueAtLeast_of_cofinal_finite_extractions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:47:27.935667+00:00
-- url     : https://prove2.me/theorems/e0f2d25d-b38c-4703-a909-44ac64191b68
-- title:
--   Cofinal finite matrix-product extractions imply a tau-value bound
-- statement:
--   Let $T$ be an order-three tensor over a field, let $\tau\in\mathbb R$, and let $V\ge0$. Suppose there is a sequence of tensor powers $s(n)\to\infty$ and relative errors $e_n\to0$ such that, for all sufficiently large $n$, $T^{\otimes s(n)}$ restricts to a finite direct sum of matrix-multiplication tensors and
--
--   $$
--   V^{s(n)}(1-e_n)\le\sum_i(a_{n,i}b_{n,i}c_{n,i})^\tau.
--   $$
--
--   Then $T$ has tau-value at least $V$. This theorem is the reusable passage from cofinal, finite laser-method extractions to an asymptotic tau-value witness; it preserves the concrete restrictions and places no uniform bound on the number of surviving matrix products.
--
--   **Formalization Note** The cofinality hypothesis prevents a bounded sequence of powers from supplying a spurious asymptotic witness. The conclusion is the witness-level predicate `HasTauValueAtLeast`, not a scalar surrogate.
-- source:
--   Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), definition of value on journal p. 264 and cofinal finite-power extractions on journal pp. 267--272; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_mme_tau_value
open MME BigOperators Filter
universe u

theorem mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    {K : Type u} [Field K]
    (T : TensorObj K 3) (tau V : ℝ) (hV : 0 ≤ V)
    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (hextract :
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            (T.kronPow (s n)) ∧
          V ^ (s n) * (1 - error n) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) :
    HasTauValueAtLeast T tau V := by sorry
