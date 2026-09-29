-- Prove2me | Theorems.Thm_mme_Ctensor_three_one_H_one_cyclic_value_below
-- name    : mme_Ctensor_three_one_H_one_cyclic_value_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T04:34:50.919838+00:00
-- url     : https://prove2.me/theorems/2c26087b-03aa-4137-a5dd-0a01286d5993
-- title:
--   Strict value bounds for a heterogeneous cyclic triple of C-tensors
-- statement:
--   Let $X,Y,Z$ be three possibly distinct C-tensors over $\langle1,H,1\rangle$, with $H>0$.  Suppose all component matrix products in all three tensors have one positive common volume $v$.  For $3\tau\ge2$, every nonnegative strict sub-bound
--
--   $$
--   0\le V<H^2(v^3)^\tau
--   $$
--
--   is attained by the tau-value of the heterogeneous cyclic product $X\otimes\pi(Y)\otimes\pi^2(Z)$.
--
--   The proof uses balanced component words and an induced matching exactly as in the ordinary one-C-tensor theorem.  The three tensors need not share component dimensions or fine-coordinate identifications: after cyclic multiplication, only the product of their three common volumes enters.
-- source:
--   V. Strassen's C-tensor value method, in the heterogeneous form required by the disjoint C-tensor family in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271--272; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_threeStarCyclicProduct
import Definitions.Def_mme_tau_value

open MME

universe u

theorem mme_Ctensor_three_one_H_one_cyclic_value_below
    {K : Type u} [Field K]
    {X Y Z : TensorObj K 3} {H volume : ℕ}
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (hH : 0 < H) (hvolume : 0 < volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < (H : ℝ) ^ 2 * (((volume ^ 3 : ℕ) : ℝ) ^ tau)) :
    HasTauValueAtLeast (threeStarCyclicProduct X Y Z) tau V := by
  sorry
