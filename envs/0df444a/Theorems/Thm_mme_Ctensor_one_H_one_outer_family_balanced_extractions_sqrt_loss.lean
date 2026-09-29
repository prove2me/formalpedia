-- Prove2me | Theorems.Thm_mme_Ctensor_one_H_one_outer_family_balanced_extractions_sqrt_loss
-- name    : mme_Ctensor_one_H_one_outer_family_balanced_extractions_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T04:47:14.061095+00:00
-- url     : https://prove2.me/theorems/63f53c34-5a47-408e-91cf-15b5e837120b
-- title:
--   Doubly balanced finite extractions from a family of C-tensors
-- statement:
--   Let $T$ restrict to a direct sum of $A>0$ C-tensors over $\langle1,H,1\rangle$, with $H>0$ and one positive common component volume $v$. For $3\tau\ge2$, there is a constant $C\ge0$ such that, for all sufficiently large $m$ and $R=A^3Hm$, the $R$-th power of the cyclic symmetrization of $T$ restricts to a direct sum of matrix-multiplication tensors whose total $\tau$-weight is at least
--
--   $$
--   \left(A^3H^2(v^3)^\tau\right)^R
--   \exp\left(-C\sqrt{R+1}\right).
--   $$
--
--   The proof balances twice: first among the $A^3$ ordered triples of outer C-tensor stars, and then among the $H$ inner components of each star. The subexponential losses from the two balanced-type counts and the Salem--Spencer extraction are absorbed into the displayed square-root term. This is the finite-extraction form of the Coppersmith--Winograd outer C-tensor sum argument.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271--272.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

theorem mme_Ctensor_one_H_one_outer_family_balanced_extractions_sqrt_loss
    {K : Type u} [Field K]
    {T : TensorObj K 3} {A H volume : ℕ}
    (stars : CTensorOneHOneFamilyCertificate T A H volume)
    (hA : 0 < A) (hH : 0 < H) (hvolume : 0 < volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let R : ℕ := A ^ 3 * H * m
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            ((cyclicSymmetrization T).kronPow R) ∧
          ((((A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
                (((volume ^ 3 : ℕ) : ℝ) ^ tau)) ^ R) *
              Real.exp
                (-C * Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) := by
  sorry
