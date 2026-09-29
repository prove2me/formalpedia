-- Prove2me | Theorems.Thm_mme_finite_MM_extractions_kronFin_replicate
-- name    : mme_finite_MM_extractions_kronFin_replicate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T05:08:51.718698+00:00
-- url     : https://prove2.me/theorems/498935d8-a66a-4fe7-9ec0-86c16e36e61a
-- title:
--   Finite products and replicas of uniform MM extraction families
-- statement:
--   Let $Y_1,\ldots,Y_n$ be a nonempty finite family of order-three tensors. Suppose every $Y_p$ restricts to at least $L\ge0$ matrix-multiplication tensors and every extracted tensor has dimension product exactly $V$. For any nonnegative integer $W$, the direct sum of $W$ copies of $\bigotimes_pY_p$ restricts to a direct sum of $k$ matrix-multiplication tensors satisfying
--
--   $$
--   WL^n\le k,\qquad a_i b_i c_i=V^n\quad(1\le i\le k).
--   $$
--
--   This is the finite distributive and flattening step: choose one extracted matrix product from each factor, use the Kronecker product identity for matrix-multiplication tensors, enumerate the Cartesian product of the finite index families, and repeat the resulting family $W$ times. No balanced-word or asymptotic argument occurs in this statement.
-- source:
--   The finite direct-sum and Kronecker-product assembly used in V. Strassen's C-tensor value method and D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271–272; https://doi.org/10.1016/S0747-7171(08)80013-2. The matrix-product flattening is the standard identity $\langle a,b,c\rangle\otimes\langle a',b',c'\rangle\cong\langle aa',bb',cc'\rangle$.

import Mathlib.Data.Fintype.Card
import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_tensor_rank

open MME BigOperators

universe u

theorem mme_finite_MM_extractions_kronFin_replicate
    {K : Type u} [Field K]
    {n W V : ℕ} (Y : Fin n → TensorObj K 3)
    (L : ℝ) (hn : 0 < n) (hL : 0 ≤ L)
    (hextract : ∀ p : Fin n,
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
          (Y p) ∧
        L ≤ (k : ℝ) ∧
        (∀ i, a i * b i * c i = V)) :
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
        (TensorObj.bigAdd (fun _ : Fin W => TensorObj.kronFin n Y)) ∧
      (W : ℝ) * L ^ n ≤ (k : ℝ) ∧
      (∀ i, a i * b i * c i = V ^ n) := by
  sorry
