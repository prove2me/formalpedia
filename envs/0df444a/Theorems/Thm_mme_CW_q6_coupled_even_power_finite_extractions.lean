-- Prove2me | Theorems.Thm_mme_CW_q6_coupled_even_power_finite_extractions
-- name    : mme_CW_q6_coupled_even_power_finite_extractions
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-24T05:02:02.070844+00:00
-- url     : https://prove2.me/theorems/50c8808b-33c2-4b14-8cd3-6afb3d710f89
-- title:
--   Even-power Salem--Spencer extraction for the coupled $q=6$ constituent
-- statement:
--   Fix $\tau$ with $3\tau\ge2$ and let $D_6$ be the explicit four-sum coupled Coppersmith--Winograd constituent. For every sufficiently large $N$, set
--
--   $$
--   \lambda=\frac{2}{6^{3\tau}+2},\qquad
--   L=\lfloor\lambda N\rfloor,\qquad G=N-L.
--   $$
--
--   Then $L>0$, $L+G=N$, and the exact cross-multiplied pruning condition $341L<100G$ holds. There is an error sequence $e_N\to0$, eventually satisfying $0\le e_N<1$, and a finite family of matrix-multiplication tensors such that
--
--   $$
--   \bigoplus_i\langle a_{N,i},b_{N,i},c_{N,i}\rangle
--   \;\leq_{\mathrm{Restrict}}\;
--   \bigl(D_6\otimes\pi(D_6)\otimes\pi^2(D_6)\bigr)^{\otimes 2N}
--   $$
--
--   and
--
--   $$
--   \bigl(4\,6^{3\tau}(6^{3\tau}+2)\bigr)^{2N}(1-e_N)
--   \le\sum_i(a_{N,i}b_{N,i}c_{N,i})^{\tau}.
--   $$
--
--   This is the finite, witness-level content of the Salem--Spencer hashing and collision-pruning argument on journal pp. 270--272. It keeps the literal even tensor power, the rounded block parameters, every surviving matrix-product dimension, and the actual direct-sum restriction; no scalar or entropy-only surrogate replaces the extraction.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), proof of the coupled-constituent lemma on journal pp. 270--272 (PDF pp. 20--22), including the 2N-th power, L/G choice, Salem--Spencer hashing, pruning, and final value estimate; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_CW_coupled_value
open MME BigOperators Filter
universe u

theorem mme_CW_q6_coupled_even_power_finite_extractions
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ error : ℕ → ℝ,
      Tendsto error atTop (nhds 0) ∧
      ∀ᶠ N : ℕ in atTop,
        let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
        let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
        let G : ℕ := N - L
        0 ≤ error N ∧ error N < 1 ∧
        0 < L ∧ L + G = N ∧ 341 * L < 100 * G ∧
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
          (4 * (6 : ℝ) ^ (3 * tau) *
              ((6 : ℝ) ^ (3 * tau) + 2)) ^ (2 * N) *
              (1 - error N) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by sorry
