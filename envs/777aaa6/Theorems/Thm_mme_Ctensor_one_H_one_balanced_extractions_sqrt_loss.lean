-- Prove2me | Theorems.Thm_mme_Ctensor_one_H_one_balanced_extractions_sqrt_loss
-- name    : mme_Ctensor_one_H_one_balanced_extractions_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T02:16:31.481466+00:00
-- url     : https://prove2.me/theorems/45754b61-d227-40c7-986d-086502b8b756
-- title:
--   Balanced finite extractions from a cyclic C-tensor with square-root loss
-- statement:
--   Let $T$ be a C-tensor over $\langle1,H,1\rangle$ whose $H>0$ matrix-multiplication components all have the same positive volume $v$. Fix $\tau$ with $3\tau\ge2$. Then there is a constant $C\ge0$ such that, for all sufficiently large $m$, with $R=Hm$, the $R$-th power of the cyclic symmetrization restricts to a concrete finite direct sum of matrix-multiplication tensors whose total $\tau$-weight is at least
--
--   $$
--   \bigl(H^2(v^3)^\tau\bigr)^R\exp(-C\sqrt{R+1}).
--   $$
--
--   This is the finite heart of Strassen's C-tensor value argument. One first restricts each cyclic orientation to the balanced word type in which every component occurs $m$ times. The three component products have common total volume $v^{3R}$. The resulting coarse matrix-multiplication support then admits a Behrend induced matching of size $H^{2R-o(R)}$, making the surviving fine blocks mode-disjoint. The square-root envelope absorbs the multinomial and induced-matching losses without claiming exact endpoint attainment.
-- source:
--   V. Strassen's C-tensor value method as applied in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271--272; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_mme_tau_value
import Definitions.Def_mme_CW_coupled_value

open MME BigOperators Filter

universe u

theorem mme_Ctensor_one_H_one_balanced_extractions_sqrt_loss
    {K : Type u} [Field K]
    {T : TensorObj K 3} {H volume : ℕ}
    (cert : CTensorOneHOneCertificate T H volume)
    (hH : 0 < H) (hvolume : 0 < volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let R : ℕ := H * m
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            ((cyclicSymmetrization T).kronPow R) ∧
          (((H : ℝ) ^ 2 *
                (((volume ^ 3 : ℕ) : ℝ) ^ tau)) ^ R) *
              Real.exp
                (-C * Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  sorry
