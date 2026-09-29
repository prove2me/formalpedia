-- Prove2me | solution 2 for mme_HasSixSymmetricTauValueAtLeast_of_powered_cyclic_source_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T13:16:54.416147+00:00
-- url     : https://prove2.me/submissions/d60461ba-b6da-4bce-a166-fe0cd150ebfa

import Mathlib.Tactic
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_finite_kronFin_HasTauValueAtLeast_product_below
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

universe u

private theorem kronFin_const_isomorphic_kronPow
    {K : Type u} [Field K] (T : TensorObj K 3) (N : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.kronFin N (fun _ ↦ T)) (T.kronPow N) := by
  apply (TensorQ.toQ_eq_iff).1
  rw [mme_toQ_kronFin, TensorQ.toQ_kronPow]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem HasTauValueAtLeast_kronPow_below
    {K : Type u} [Field K] (T : TensorObj K 3)
    (tau base target : ℝ) (N : ℕ)
    (hbase : 0 < base) (htarget : 0 ≤ target)
    (hstrict : target < base)
    (hvalue : HasTauValueAtLeast T tau base) :
    HasTauValueAtLeast (T.kronPow N) tau (target ^ N) := by
  have hproduct : HasTauValueAtLeast
      (TensorObj.kronFin N (fun _ ↦ T)) tau
      (∏ _ : Fin N, target) :=
    mme_finite_kronFin_HasTauValueAtLeast_product_below
      (fun _ : Fin N ↦ T) tau
      (fun _ ↦ base) (fun _ ↦ target)
      (fun _ ↦ hbase) (fun _ ↦ htarget)
      (fun _ ↦ hstrict) (fun _ ↦ hvalue)
  have htransport := mme_HasTauValueAtLeast_mono_restrict
    (kronFin_const_isomorphic_kronPow T N).1 hproduct
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    using htransport

private theorem kronFin_two_isomorphic_kron
    {K : Type u} [Field K] (A B : TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kronFin 2 (![A, B] : Fin 2 → TensorObj K 3))
      (TensorObj.kron A B) := by
  apply (TensorQ.toQ_eq_iff).1
  rw [mme_toQ_kronFin, TensorQ.toQ_kron]
  simp [Fin.prod_univ_succ]

theorem solution
    {K : Type u} [Field K]
    (source targetObj : TensorObj K 3) (tau endpoint target : ℝ)
    (N : ℕ)
    (hN : 0 < N)
    (hendpoint : 0 < endpoint) (htarget : 0 ≤ target)
    (hstrict : target < endpoint)
    (hsource : ∀ W : ℝ, 0 ≤ W → W < endpoint →
      HasTauValueAtLeast source tau (W ^ (3 : ℕ)))
    (hleft : TensorObj.Restrict (source.kronPow N)
      (cyclicSymmetrization targetObj))
    (hright : TensorObj.Restrict (source.kronPow N)
      (TensorObj.permObj swapFirstTwoPerm
        (cyclicSymmetrization targetObj))) :
    HasSixSymmetricTauValueAtLeast targetObj tau (target ^ N) := by
  let upper : ℝ := (target + endpoint) / 2
  let inner : ℝ := (target + upper) / 2
  have htargetUpper : target < upper := by
    dsimp only [upper]
    linarith
  have hupperEndpoint : upper < endpoint := by
    dsimp only [upper]
    linarith
  have htargetInner : target < inner := by
    dsimp only [inner]
    linarith
  have hinnerUpper : inner < upper := by
    dsimp only [inner]
    linarith
  have hupper : 0 < upper := lt_of_le_of_lt htarget htargetUpper
  have hinner : 0 < inner := lt_of_le_of_lt htarget htargetInner
  have hsourceUpper :
      HasTauValueAtLeast source tau (upper ^ (3 : ℕ)) :=
    hsource upper hupper.le hupperEndpoint
  have hinnerCube : inner ^ (3 : ℕ) < upper ^ (3 : ℕ) :=
    pow_lt_pow_left₀ hinnerUpper hinner.le (by norm_num)
  have hpowered :
      HasTauValueAtLeast (source.kronPow N) tau
        ((inner ^ (3 : ℕ)) ^ N) :=
    HasTauValueAtLeast_kronPow_below source tau
      (upper ^ (3 : ℕ)) (inner ^ (3 : ℕ)) N
      (pow_pos hupper 3) (pow_nonneg hinner.le 3)
      hinnerCube hsourceUpper
  have hleftValue : HasTauValueAtLeast
      (cyclicSymmetrization targetObj) tau
      ((inner ^ (3 : ℕ)) ^ N) :=
    mme_HasTauValueAtLeast_mono_restrict hleft hpowered
  have hrightValue : HasTauValueAtLeast
      (TensorObj.permObj swapFirstTwoPerm
        (cyclicSymmetrization targetObj)) tau
      ((inner ^ (3 : ℕ)) ^ N) :=
    mme_HasTauValueAtLeast_mono_restrict hright hpowered
  let factor : Fin 2 → TensorObj K 3 :=
    ![cyclicSymmetrization targetObj,
      TensorObj.permObj swapFirstTwoPerm
        (cyclicSymmetrization targetObj)]
  let baseValue : ℝ := (inner ^ (3 : ℕ)) ^ N
  let targetValue : ℝ := (target ^ (3 : ℕ)) ^ N
  have htargetCubeInnerCube :
      target ^ (3 : ℕ) < inner ^ (3 : ℕ) :=
    pow_lt_pow_left₀ htargetInner htarget (by norm_num)
  have htargetValueBase : targetValue < baseValue := by
    dsimp only [targetValue, baseValue]
    exact pow_lt_pow_left₀ htargetCubeInnerCube
      (pow_nonneg htarget 3) hN.ne'
  have hbaseValue : 0 < baseValue := by
    dsimp only [baseValue]
    positivity
  have htargetValue : 0 ≤ targetValue := by
    dsimp only [targetValue]
    positivity
  have htwo : HasTauValueAtLeast (TensorObj.kronFin 2 factor) tau
      (∏ _ : Fin 2, targetValue) := by
    apply mme_finite_kronFin_HasTauValueAtLeast_product_below
      factor tau (fun _ ↦ baseValue) (fun _ ↦ targetValue)
      (fun _ ↦ hbaseValue) (fun _ ↦ htargetValue)
      (fun _ ↦ htargetValueBase)
    intro i
    fin_cases i
    · exact hleftValue
    · exact hrightValue
  change HasTauValueAtLeast (sixSymmetrization targetObj) tau
    ((target ^ N) ^ (6 : ℕ))
  have hpow : targetValue ^ (2 : ℕ) =
      (target ^ N) ^ (6 : ℕ) := by
    dsimp only [targetValue]
    calc
      ((target ^ 3) ^ N) ^ 2 = target ^ ((3 * N) * 2) := by
        rw [← pow_mul target 3 N]
        exact (pow_mul target (3 * N) 2).symm
      _ = target ^ (N * 6) := by congr 1; omega
      _ = (target ^ N) ^ 6 := pow_mul target N 6
  have htwo' : HasTauValueAtLeast (sixSymmetrization targetObj) tau
      (∏ _ : Fin 2, targetValue) :=
    mme_HasTauValueAtLeast_mono_restrict
      (kronFin_two_isomorphic_kron
        (cyclicSymmetrization targetObj)
        (TensorObj.permObj swapFirstTwoPerm
          (cyclicSymmetrization targetObj))).1 htwo
  simpa only [Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, hpow] using htwo'
