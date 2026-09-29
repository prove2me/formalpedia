-- Prove2me | Theorems.Thm_mme_Ctensor_three_one_H_one_balanced_extractions_sqrt_loss
-- name    : mme_Ctensor_three_one_H_one_balanced_extractions_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T04:36:19.346013+00:00
-- url     : https://prove2.me/theorems/0c563883-a0d6-4a52-8385-5171803ced02
-- title:
--   Balanced finite extractions from three heterogeneous C-tensors
-- statement:
--   Let $X,Y,Z$ be three C-tensors over $\langle1,H,1\rangle$, where $H>0$, and suppose every component in every tensor has the same positive matrix-product volume $v$.  For $3\tau\ge2$, there is a constant $C\ge0$ such that, with $R=Hm$ and all sufficiently large $m$, the $R$-th power of $X\otimes\pi(Y)\otimes\pi^2(Z)$ restricts to a finite direct sum of matrix-multiplication tensors whose total tau-weight is at least
--
--   $$
--   \bigl(H^2(v^3)^\tau\bigr)^R e^{-C\sqrt{R+1}}.
--   $$
--
--   This is the finite balanced-type and induced-matching core of the heterogeneous C-tensor value theorem.  The bound is uniform in the component shapes and uses only their common volume.
-- source:
--   Strassen's balanced C-tensor value method in the heterogeneous form needed for Coppersmith--Winograd's disjoint C-tensor family; D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271--272; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_threeStarCyclicProduct
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

theorem mme_Ctensor_three_one_H_one_balanced_extractions_sqrt_loss
    {K : Type u} [Field K]
    {X Y Z : TensorObj K 3} {H volume : ℕ}
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (hH : 0 < H) (hvolume : 0 < volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let R : ℕ := H * m
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            ((threeStarCyclicProduct X Y Z).kronPow R) ∧
          (((H : ℝ) ^ 2 *
                (((volume ^ 3 : ℕ) : ℝ) ^ tau)) ^ R) *
              Real.exp
                (-C * Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  sorry
