-- Prove2me | Theorems.Thm_mme_Ctensor_one_half_family_to_six_finite_extraction
-- name    : mme_Ctensor_one_half_family_to_six_finite_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:47:03.720589+00:00
-- url     : https://prove2.me/theorems/407e3a1c-09c1-4598-b5ba-9d3022f81552
-- title:
--   One-half C-tensor hashing completes to a six-symmetric finite extraction
-- statement:
--   Let an order-three tensor contain a source-faithful family of $A$ C-tensor stars of type $\langle1,H,1\rangle$, with every component having common volume $v$. If $0<H\le4^N$, then the full six-symmetrization contains a finite direct sum of matrix-multiplication tensors whose total $\tau$-weight is at least
--
--   $$
--   \left(A^3H^2e^{-200\sqrt{N+1}}\right)^2\left(v^6\right)^\tau.
--   $$
--
--   The construction first finishes the ordinary cyclic MM extraction and only then tensors it with its first-two-mode swap. Thus every Cartesian pair survives and no pre-cyclic mixed-choice assumption is needed.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Lemma 4.6(d) and Appendix A; the post-cyclic Cartesian tensor product is elementary multilinear algebra.

import Mathlib
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_direct_finite_extraction
import Theorems.Thm_mme_behrend_log_loss_absorbed_sqrt
import Theorems.Thm_mme_finite_MM_extraction_swap_double_uniform

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_Ctensor_one_half_family_to_six_finite_extraction
    {K : Type u} [Field K]
    {T : TensorObj K 3} (tau : ℝ) (N A H volume : ℕ)
    (stars : CTensorOneHOneFamilyCertificate T A H volume)
    (hH : 0 < H) (hHbound : H ≤ 4 ^ N) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization T) ∧
      (((((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
            Real.exp (-200 * Real.sqrt (((N + 1 : ℕ) : ℝ)))) ^
          (2 : ℕ)) *
          (((((volume ^ 3) ^ 2 : ℕ) : ℝ)) ^ tau) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  sorry
