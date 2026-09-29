-- Prove2me | solution 1 for mme_stothers_phi116_profile_source_cyclic_value_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:56:39.564317+00:00
-- url     : https://prove2.me/submissions/3fd7329c-c161-4ec7-ad49-8a31fa228123

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi116_exact_address_factorization_data
import Theorems.Thm_mme_CW_q6_coupled_raw_cyclic_value_below
import Theorems.Thm_mme_finite_kronFin_cyclic_value_product_below
import Theorems.Thm_mme_stothers_phi116_rectangular_component_cyclic_value

open MME BigOperators
open MME.StothersFourth MME.StothersFourth.Phi116

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem kronFin_const_eq_kronPow
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) :
    ∀ n : ℕ, TensorObj.kronFin n (fun _ ↦ T) = T.kronPow n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change TensorObj.kron T
          (TensorObj.kronFin n (fun _ ↦ T)) =
        TensorObj.kron T (T.kronPow n)
      rw [ih]

private theorem cyclic_kronPow_value_below
    {K : Type u} [Field K]
    (T : TensorObj K 3) (tau B W : ℝ)
    (hB : 0 < B) (hW : 0 ≤ W) (hWB : W < B)
    (hvalue : HasTauValueAtLeast (cyclicSymmetrization T) tau B)
    (n : ℕ) :
    HasTauValueAtLeast (cyclicSymmetrization (T.kronPow n)) tau
      (W ^ n) := by
  have h := mme_finite_kronFin_cyclic_value_product_below
    (fun _ : Fin n ↦ T) tau (fun _ ↦ B) (fun _ ↦ W)
      (fun _ ↦ hB) (fun _ ↦ hW) (fun _ ↦ hWB) (fun _ ↦ hvalue)
  simpa only [kronFin_const_eq_kronPow, Fin.prod_const] using h

theorem solution
    {K : Type u} [Field K] (tau : ℝ)
    (htau : 2 ≤ 3 * tau)
    (alpha beta : ℕ)
    (W : Fin 4 → ℝ)
    (hWpos : ∀ r, 0 < W r)
    (hWcoupled : W 0 < L 6 tau ∧ W 1 < L 6 tau)
    (hWrect : W 2 < E 6 tau ^ (2 : ℕ) ∧
      W 3 < E 6 tau ^ (2 : ℕ)) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kronFin 4 (fun r ↦
          (phi116ComponentObj K r).kronPow
            (phi116ComponentMultiplicity alpha beta r)))) tau
      (∏ r : Fin 4,
        (W r ^ phi116ComponentMultiplicity alpha beta r) / 2) := by
  have hL : 0 < L 6 tau := by
    unfold L
    positivity
  have hE2 : 0 < E 6 tau ^ (2 : ℕ) := by
    unfold E
    positivity
  have hcomponent : ∀ r : Fin 4,
      HasTauValueAtLeast
        (cyclicSymmetrization
          ((phi116ComponentObj K r).kronPow
            (phi116ComponentMultiplicity alpha beta r))) tau
        (W r ^ phi116ComponentMultiplicity alpha beta r) := by
    intro r
    fin_cases r
    · let B := (W 0 + L 6 tau) / 2
      have hB : 0 < B := by dsimp only [B]; linarith [hWpos 0]
      have hWB : W 0 < B := by dsimp only [B]; linarith [hWcoupled.1]
      have hBL : B < L 6 tau := by dsimp only [B]; linarith [hWcoupled.1]
      have hbase := mme_CW_q6_coupled_raw_cyclic_value_below
        (K := K) tau htau B (le_of_lt hB)
        (by simpa only [L] using hBL)
      simpa only [phi116ComponentObj] using
        cyclic_kronPow_value_below (coupledObj K 6) tau B (W 0)
          hB (le_of_lt (hWpos 0)) hWB hbase
          (phi116ComponentMultiplicity alpha beta 0)
    · let B := (W 1 + L 6 tau) / 2
      have hB : 0 < B := by dsimp only [B]; linarith [hWpos 1]
      have hWB : W 1 < B := by dsimp only [B]; linarith [hWcoupled.2]
      have hBL : B < L 6 tau := by dsimp only [B]; linarith [hWcoupled.2]
      have hbase := mme_CW_q6_coupled_raw_cyclic_value_below
        (K := K) tau htau B (le_of_lt hB)
        (by simpa only [L] using hBL)
      simpa only [phi116ComponentObj] using
        cyclic_kronPow_value_below (coupledObj K 6) tau B (W 1)
          hB (le_of_lt (hWpos 1)) hWB hbase
          (phi116ComponentMultiplicity alpha beta 1)
    · have hbase :=
        mme_stothers_phi116_rectangular_component_cyclic_value
          (K := K) tau
      simpa only [phi116ComponentObj] using
        cyclic_kronPow_value_below (MMObj K 12 1 12) tau
          (E 6 tau ^ (2 : ℕ)) (W 2) hE2
          (le_of_lt (hWpos 2)) hWrect.1 hbase
          (phi116ComponentMultiplicity alpha beta 2)
    · have hbase :=
        mme_stothers_phi116_rectangular_component_cyclic_value
          (K := K) tau
      simpa only [phi116ComponentObj] using
        cyclic_kronPow_value_below (MMObj K 12 1 12) tau
          (E 6 tau ^ (2 : ℕ)) (W 3) hE2
          (le_of_lt (hWpos 3)) hWrect.2 hbase
          (phi116ComponentMultiplicity alpha beta 3)
  exact mme_finite_kronFin_cyclic_value_product_below
    (fun r : Fin 4 ↦
      (phi116ComponentObj K r).kronPow
        (phi116ComponentMultiplicity alpha beta r)) tau
    (fun r ↦ W r ^ phi116ComponentMultiplicity alpha beta r)
    (fun r ↦ (W r ^ phi116ComponentMultiplicity alpha beta r) / 2)
    (fun r ↦ pow_pos (hWpos r) _)
    (fun r ↦ div_nonneg (pow_nonneg (le_of_lt (hWpos r)) _) (by norm_num))
    (fun r ↦ by
      have hp := pow_pos (hWpos r) (phi116ComponentMultiplicity alpha beta r)
      linarith)
    hcomponent
