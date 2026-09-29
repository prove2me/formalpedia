-- Prove2me | solution 1 for MME.StothersFourth.Phi233.mme_stothers_phi233_doubled_hash_AP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:27:35.53655+00:00
-- url     : https://prove2.me/submissions/94ecb0f1-2881-4dd6-84a5-d519d283c4ee

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash

open BigOperators
open MME.StothersFourth.Phi233

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {R : Type} [CommRing R] {N : ℕ}
    (b : R) (w : Fin (2 * N) → R)
    (x : ProfileAddress N) (hsupp : CoordinatewiseSupported x) :
    doubledXHash b w (x 0) + doubledYHash b w (x 1) =
      2 * doubledZHash b w (x 2) := by
  have hsum (j : Fin (2 * N)) :
      (x 0 j).val + (x 1 j).val + (x 2 j).val = 4 := by
    obtain ⟨r, hr⟩ := hsupp j
    have h0 := congrFun hr (0 : Fin 3)
    have h1 := congrFun hr (1 : Fin 3)
    have h2 := congrFun hr (2 : Fin 3)
    fin_cases r <;>
      simp [addressType, pattern, MME.cwSquareBlockType] at h0 h1 h2 ⊢ <;>
      omega
  have hpoint (j : Fin (2 * N)) :
      ((2 * (x 0 j).val : ℕ) : R) * w j +
          ((2 * (x 1 j).val : ℕ) : R) * w j =
        2 * (((4 : R) - ((x 2 j).val : R)) * w j) := by
    have hr : ((x 0 j).val : R) + ((x 1 j).val : R) +
        ((x 2 j).val : R) = 4 := by
      have hr' := congrArg (fun n : ℕ ↦ (n : R)) (hsum j)
      push_cast at hr'
      exact hr'
    push_cast
    linear_combination 2 * w j * hr
  calc
    doubledXHash b w (x 0) + doubledYHash b w (x 1) =
        4 * b +
          ((∑ j, ((2 * (x 0 j).val : ℕ) : R) * w j) +
            ∑ j, ((2 * (x 1 j).val : ℕ) : R) * w j) := by
      simp only [doubledXHash, doubledYHash]
      ring
    _ = 4 * b + ∑ j,
          (((2 * (x 0 j).val : ℕ) : R) * w j +
            ((2 * (x 1 j).val : ℕ) : R) * w j) := by
      rw [Finset.sum_add_distrib]
    _ = 4 * b + ∑ j,
          2 * (((4 : R) - ((x 2 j).val : R)) * w j) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      exact hpoint j
    _ = 2 * doubledZHash b w (x 2) := by
      rw [← Finset.mul_sum]
      simp only [doubledZHash]
      ring
