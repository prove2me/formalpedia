-- Prove2me | Theorems.Thm_mme_CW_q6_coupled_tensor_extraction_below_raw_of_pruning
-- name    : mme_CW_q6_coupled_tensor_extraction_below_raw_of_pruning
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T05:18:00.042791+00:00
-- url     : https://prove2.me/theorems/a9210702-781f-4541-ae08-9b0d24bad121
-- title:
--   Tensor-specific Salem--Spencer assembly for the coupled $q=6$ constituent
-- statement:
--   Fix $\tau$ with $3\tau\ge2$ and a nonnegative base
--
--   $$
--   V<4\,6^{3\tau}(6^{3\tau}+2).
--   $$
--
--   For a sufficiently large $N$, put $L=\lfloor2N/(6^{3\tau}+2)\rfloor$ and $G=N-L$. Assume the elementary type-count and pruning certificate
--
--   $$
--   L>0,\qquad L+G=N,\qquad 341L<100G.
--   $$
--
--   Then the Salem--Spencer hashing, collision pruning, and coupled-block assembly produce a finite family of matrix-multiplication tensors with a concrete restriction
--
--   $$
--   \bigoplus_i\langle a_{N,i},b_{N,i},c_{N,i}\rangle
--   \;\leq_{\mathrm{Restrict}}\;
--   \bigl(D_6\otimes\pi(D_6)\otimes\pi^2(D_6)\bigr)^{\otimes2N}
--   $$
--
--   and weighted volume
--
--   $$
--   V^{2N}\le\sum_i(a_{N,i}b_{N,i}c_{N,i})^{\tau}.
--   $$
--
--   This theorem is the tensor-specific core of CW90 journal pp. 270--272 after the independent floor-rounding argument has been removed. Its proof should instantiate the already formalized Salem--Spencer existence theorem and 3AP collision lemma, then construct the actual mode restrictions and direct sum. The strict sub-bound absorbs all subexponential counting losses.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled-constituent proof on journal pp. 270--272 (PDF pp. 20--22), especially the 2N-th power, Salem--Spencer hashing, shared-block pruning, C-tensor assembly, and weighted-volume estimate; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_CW_coupled_value
open MME BigOperators Filter
universe u

theorem mme_CW_q6_coupled_tensor_extraction_below_raw_of_pruning
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < 4 * (6 : ℝ) ^ (3 * tau) *
        ((6 : ℝ) ^ (3 * tau) + 2)) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let G : ℕ := N - L
      (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
          ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
        V ^ (2 * N) ≤
          ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by sorry
