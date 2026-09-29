-- Prove2me | solution 2 for CutIndexedSingleton.cutEntropy_of_isMDS
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T11:23:58.94113+00:00
-- url     : https://prove2.me/submissions/7ab32972-245b-4fc3-9b2b-b597f694f818

import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropy
import Definitions.Def_Novelty_CutIndexedSingleton
import Definitions.Def_Novelty_IITTensorNetworkEntropy

open Finset CutIndexedSingleton in
theorem solution {n q : ℕ} {C : Finset (Word n q)} {d : ℕ} (hmds : IsMDS C d)
    (hd1 : 1 ≤ d) (hdn : d ≤ n + 1) (hq : 0 < q) (S : Finset (Fin n)) :
    cutEntropy C S = (min S.card (CutData.sdim n d) : ℕ) * Real.log q := by
  classical
  obtain ⟨hmin, hcard⟩ := hmds
  set k := CutData.sdim n d with hk
  have hkn : k ≤ n := by
    simp only [hk, CutData.sdim]
    omega
  -- codewords are determined by their restriction to any set of at least `k` sites
  have hinjG : ∀ T : Finset (Fin n), k ≤ T.card →
      ∀ c ∈ C, ∀ c' ∈ C, (∀ i ∈ T, c i = c' i) → c = c' := by
    intro T hT c hc c' hc' hagree
    by_contra hne
    have h1 := hmin c hc c' hc' hne
    have h2 : hammingDist c c' ≤ Tᶜ.card := by
      unfold hammingDist
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_compl]
      intro hiT
      exact hi (hagree i hiT)
    rw [Finset.card_compl, Fintype.card_fin] at h2
    have hTn : T.card ≤ n := by simpa using Finset.card_le_univ T
    simp only [hk, CutData.sdim] at hT
    omega
  -- the fibres over any cut partition the code
  have hsumG : ∀ S : Finset (Fin n), C.card = ∑ z : {i // i ∈ S} → Fin q, (fiber C S z).card := by
    intro S
    rw [Finset.card_eq_sum_card_fiberwise (s := C) (t := univ) (f := proj S)
      (fun _ _ => Finset.mem_univ _)]
    rfl
  -- fibres over small cuts all have the same size
  have hfib : ∀ S : Finset (Fin n), S.card ≤ k → ∀ y : {i // i ∈ S} → Fin q,
      (fiber C S y).card = q ^ (k - S.card) := by
    intro S hS y
    obtain ⟨T, hST, hTk⟩ := Finset.exists_superset_card_eq hS (by simpa using hkn)
    have hinjT := hinjG T (by omega)
    have hTS : (T \ S).card = k - S.card := by
      have := Finset.card_sdiff_add_card_eq_card hST
      omega
    have hle : ∀ z : {i // i ∈ S} → Fin q, (fiber C S z).card ≤ q ^ (k - S.card) := by
      intro z
      have hcardF : (univ : Finset ({i // i ∈ T \ S} → Fin q)).card = q ^ (k - S.card) := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, hTS]
      rw [← hcardF]
      apply Finset.card_le_card_of_injOn (fun c => fun i : {i // i ∈ T \ S} => c i.1)
      · intro c _
        exact Finset.mem_univ _
      · intro c hc c' hc' heq
        rw [Finset.mem_coe, fiber, Finset.mem_filter] at hc hc'
        apply hinjT c hc.1 c' hc'.1
        intro i hiT
        by_cases hiS : i ∈ S
        · have e1 := congrFun hc.2 ⟨i, hiS⟩
          have e2 := congrFun hc'.2 ⟨i, hiS⟩
          simp only [proj] at e1 e2
          rw [e1, e2]
        · have := congrFun heq ⟨i, Finset.mem_sdiff.2 ⟨hiT, hiS⟩⟩
          simpa using this
    apply le_antisymm (hle y)
    by_contra hlt
    have hlt' : (fiber C S y).card < q ^ (k - S.card) := not_le.1 hlt
    have hs := Finset.sum_lt_sum (s := univ) (f := fun z => (fiber C S z).card)
      (g := fun _ => q ^ (k - S.card)) (fun z _ => hle z) ⟨y, Finset.mem_univ y, hlt'⟩
    rw [← hsumG S, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_coe,
      Fintype.card_fin, smul_eq_mul, ← pow_add, show S.card + (k - S.card) = k by omega] at hs
    omega
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hC0 : (C.card : ℝ) ≠ 0 := by
    rw [hcard]
    exact_mod_cast (pow_pos hq _).ne'
  unfold cutEntropy cutProb
  rcases le_total S.card k with hSk | hkS
  · rw [min_eq_left hSk]
    have hqs : (q : ℝ) ^ S.card ≠ 0 := pow_ne_zero _ hq'.ne'
    have hratio : (q : ℝ) ^ (k - S.card) / (q : ℝ) ^ k = 1 / (q : ℝ) ^ S.card := by
      rw [div_eq_div_iff (pow_ne_zero _ hq'.ne') hqs, one_mul, ← pow_add,
        Nat.sub_add_cancel hSk]
    have e : ∀ y : {i // i ∈ S} → Fin q,
        Real.negMulLog (((fiber C S y).card : ℝ) / (C.card : ℝ))
          = 1 / (q : ℝ) ^ S.card * Real.log ((q : ℝ) ^ S.card) := by
      intro y
      rw [hfib S hSk y, hcard, Nat.cast_pow, Nat.cast_pow, hratio]
      unfold Real.negMulLog
      rw [one_div, Real.log_inv]
      ring
    rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow,
      ← mul_assoc, mul_one_div_cancel hqs, one_mul, Real.log_pow]
  · rw [min_eq_right hkS]
    have h01 : ∀ y : {i // i ∈ S} → Fin q, (fiber C S y).card ≤ 1 := by
      intro y
      apply Finset.card_le_one.2
      intro a ha b hb
      rw [fiber, Finset.mem_filter] at ha hb
      apply hinjG S hkS a ha.1 b hb.1
      intro i hi
      have := congrFun (ha.2.trans hb.2.symm) ⟨i, hi⟩
      simpa [proj] using this
    have e : ∀ y : {i // i ∈ S} → Fin q,
        Real.negMulLog (((fiber C S y).card : ℝ) / (C.card : ℝ))
          = ((fiber C S y).card : ℝ) / (C.card : ℝ) * Real.log (C.card : ℝ) := by
      intro y
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (h01 y) with h | h
      · rw [h]
        simp
      · rw [h, Nat.cast_one]
        unfold Real.negMulLog
        rw [one_div, Real.log_inv]
        ring
    rw [Finset.sum_congr rfl (fun y _ => e y), ← Finset.sum_mul, ← Finset.sum_div,
      ← Nat.cast_sum, ← hsumG S, div_self hC0, one_mul, hcard, Nat.cast_pow, Real.log_pow]
