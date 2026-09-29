-- Prove2me | solution 2 for CutIndexedSingleton.isMDS_iff_cutEntropy_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T11:33:33.882126+00:00
-- url     : https://prove2.me/submissions/f5c45030-d016-4ea1-8e5a-7b94851f8e28

import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropy
import Definitions.Def_Novelty_CutIndexedSingleton
import Definitions.Def_Novelty_IITTensorNetworkEntropy

open Finset CutIndexedSingleton in
theorem solution {n q : ℕ} {C : Finset (Word n q)} {d : ℕ} (hC : C.Nonempty)
    (hd : MinDist C d) (hd1 : 1 ≤ d) (hdn : d ≤ n + 1) (hq : 2 ≤ q)
    {S : Finset (Fin n)} (hS : S.card = CutData.sdim n d) :
    IsMDS C d ↔ cutEntropy C S = (CutData.sdim n d : ℕ) * Real.log q := by
  have hMDSent : IsMDS C d →
      cutEntropy C S = (min S.card (CutData.sdim n d) : ℕ) * Real.log q := by
    intro hmds
    have hq0 : 0 < q := by omega
    clear hC hd
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
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq0
    have hC0 : (C.card : ℝ) ≠ 0 := by
      rw [hcard]
      exact_mod_cast (pow_pos hq0 _).ne'
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
  classical
  have hmin := hd
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
  have hNpos : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  -- entropy is at most the log of the number of observed patterns (Jensen)
  have hent : ∀ S : Finset (Fin n), cutEntropy C S ≤ Real.log (cutRank C S) := by
    intro S
    set t := C.image (proj S) with ht
    have htpos : 0 < t.card := (hC.image _).card_pos
    have hm : (0 : ℝ) < t.card := by exact_mod_cast htpos
    have hfib0 : ∀ y, y ∉ t → (fiber C S y).card = 0 := by
      intro y hy
      rw [Finset.card_eq_zero]
      apply Finset.filter_eq_empty_iff.2
      intro c hc hcy
      exact hy (Finset.mem_image.2 ⟨c, hc, hcy⟩)
    unfold cutEntropy cutProb
    rw [← Finset.sum_subset (Finset.subset_univ t) (fun y _ hy => by
      rw [hfib0 y hy, Nat.cast_zero, zero_div, Real.negMulLog_zero])]
    have hsum1 : ∑ y ∈ t, ((fiber C S y).card : ℝ) / C.card = 1 := by
      rw [← Finset.sum_div, div_eq_one_iff_eq hNpos.ne', ← Nat.cast_sum,
        Finset.sum_subset (Finset.subset_univ t) (fun y _ hy => hfib0 y hy), ← hsumG S]
    have hJ := Real.concaveOn_negMulLog.le_map_sum (t := t) (w := fun _ => 1 / (t.card : ℝ))
      (p := fun y => ((fiber C S y).card : ℝ) / C.card) (fun _ _ => by positivity)
      (by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div_cancel hm.ne'])
      (fun y _ => Set.mem_Ici.2 (by positivity))
    simp only [smul_eq_mul] at hJ
    rw [← Finset.mul_sum, ← Finset.mul_sum, hsum1, mul_one] at hJ
    have hnm : Real.negMulLog (1 / (t.card : ℝ)) = 1 / t.card * Real.log t.card := by
      unfold Real.negMulLog
      rw [one_div, Real.log_inv]
      ring
    rw [hnm] at hJ
    have h2 := mul_le_mul_of_nonneg_left hJ hm.le
    rw [← mul_assoc, ← mul_assoc, mul_one_div_cancel hm.ne', one_mul, one_mul] at h2
    unfold cutRank
    exact h2
  -- the Singleton bound
  have hsing : C.card ≤ q ^ k := by
    obtain ⟨T, -, hTk⟩ := Finset.exists_subset_card_eq
      (show k ≤ (univ : Finset (Fin n)).card by simpa using hkn)
    have hinjT := hinjG T (by omega)
    calc C.card = (C.image (proj T)).card :=
          (Finset.card_image_of_injOn (fun c hc c' hc' h => hinjT c hc c' hc'
            (fun i hi => by
              have := congrFun h ⟨i, hi⟩
              simpa [proj] using this))).symm
      _ ≤ (univ : Finset ({i // i ∈ T} → Fin q)).card := Finset.card_le_univ _
      _ = q ^ k := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, hTk]
  have hrank_pos : ∀ S : Finset (Fin n), 0 < cutRank C S := fun S => (hC.image _).card_pos
  have hrank_C : ∀ S : Finset (Fin n), cutRank C S ≤ C.card := fun S => Finset.card_image_le
  constructor
  · intro hmds
    rw [hMDSent hmds, hS, min_self]
  · intro hE
    refine ⟨hd, le_antisymm hsing ?_⟩
    have h1 := hent S
    have h2 : (cutRank C S : ℝ) ≤ C.card := by exact_mod_cast hrank_C S
    have hr : (0 : ℝ) < cutRank C S := by exact_mod_cast hrank_pos S
    have h3 : Real.log ((q : ℝ) ^ k) ≤ Real.log (C.card : ℝ) := by
      rw [Real.log_pow]
      calc (k : ℝ) * Real.log q = cutEntropy C S := hE.symm
        _ ≤ Real.log (cutRank C S) := h1
        _ ≤ Real.log (C.card : ℝ) := Real.log_le_log hr h2
    have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
    have h4 := (Real.log_le_log_iff hqk hNpos).1 h3
    exact_mod_cast h4
