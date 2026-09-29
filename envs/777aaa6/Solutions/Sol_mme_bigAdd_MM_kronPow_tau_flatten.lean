-- Prove2me | solution 1 for mme_bigAdd_MM_kronPow_tau_flatten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:53:36.706782+00:00
-- url     : https://prove2.me/submissions/4d23d656-6b7a-4b0c-be02-71297a20128b

import Mathlib.Tactic
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_MM_word_tau_weight

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

universe u

theorem solution
    {K : Type u} [Field K]
    {k r : ℕ} (a b c : Fin k → ℕ) (tau : ℝ) :
    ∃ (q : ℕ) (A B C : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (C j)))
        ((TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i))).kronPow r) ∧
      (∑ j, (((A j * B j * C j : ℕ) : ℝ) ^ tau)) =
        (∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) ^ r := by
  classical
  let W := Fin r → Fin k
  let q := Fintype.card W
  let e : Fin q ≃ W := (Fintype.equivFin W).symm
  let A : Fin q → ℕ := fun j ↦ ∏ t, a (e j t)
  let B : Fin q → ℕ := fun j ↦ ∏ t, b (e j t)
  let C : Fin q → ℕ := fun j ↦ ∏ t, c (e j t)
  refine ⟨q, A, B, C, ?_, ?_⟩
  · exact (TensorQ.toQ_eq_iff.mp (by
      rw [TensorQ.toQ_bigAdd, TensorQ.toQ_kronPow,
        TensorQ.toQ_bigAdd, Fintype.sum_pow]
      calc
        (∑ j : Fin q, TensorQ.toQ (MMObj K (A j) (B j) (C j))) =
            ∑ p : W, TensorQ.toQ
              (MMObj K (∏ t, a (p t)) (∏ t, b (p t)) (∏ t, c (p t))) := by
          simpa only [A, B, C] using
            (Equiv.sum_comp e (fun p : W ↦ TensorQ.toQ
              (MMObj K (∏ t, a (p t)) (∏ t, b (p t)) (∏ t, c (p t)))))
        _ = ∑ p : W, ∏ t,
            TensorQ.toQ (MMObj K (a (p t)) (b (p t)) (c (p t))) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hiso := mme_kronFin_MMObj_iso (K := K) r
            (fun t ↦ a (p t)) (fun t ↦ b (p t)) (fun t ↦ c (p t))
          calc
            TensorQ.toQ
                (MMObj K (∏ t, a (p t)) (∏ t, b (p t)) (∏ t, c (p t))) =
                TensorQ.toQ (TensorObj.kronFin r
                  (fun t ↦ MMObj K (a (p t)) (b (p t)) (c (p t)))) :=
              (TensorQ.toQ_eq_iff.mpr hiso).symm
            _ = ∏ t, TensorQ.toQ
                (MMObj K (a (p t)) (b (p t)) (c (p t))) :=
              mme_toQ_kronFin _)).1
  · calc
      (∑ j : Fin q, (((A j * B j * C j : ℕ) : ℝ) ^ tau)) =
          ∑ p : W,
            ((((∏ t, a (p t)) * (∏ t, b (p t)) * (∏ t, c (p t)) : ℕ) : ℝ) ^ tau) := by
        simpa only [A, B, C] using
          (Equiv.sum_comp e (fun p : W ↦
            ((((∏ t, a (p t)) * (∏ t, b (p t)) * (∏ t, c (p t)) : ℕ) : ℝ) ^ tau)))
      _ = (∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) ^ r :=
        mme_MM_word_tau_weight a b c tau

