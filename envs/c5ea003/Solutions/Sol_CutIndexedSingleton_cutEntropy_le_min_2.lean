-- Prove2me | solution 2 for CutIndexedSingleton.cutEntropy_le_min
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T11:28:32.09963+00:00
-- url     : https://prove2.me/submissions/4af77216-13e5-4d4d-afb1-1f9e36402653

import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropy
import Definitions.Def_Novelty_CutIndexedSingleton
import Definitions.Def_Novelty_IITTensorNetworkEntropy

open Finset CutIndexedSingleton in
theorem solution {n q : ℕ} {C : Finset (Word n q)} {d : ℕ} (hC : C.Nonempty)
    (hd : MinDist C d) (hd1 : 1 ≤ d) (hq : 1 ≤ q) (S : Finset (Fin n)) :
    cutEntropy C S ≤ (min S.card (CutData.sdim n d) : ℕ) * Real.log q := by
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
  have hrank : cutRank C S ≤ q ^ (min S.card k) := by
    rcases le_total S.card k with h | h
    · rw [min_eq_left h]
      calc cutRank C S ≤ (univ : Finset ({i // i ∈ S} → Fin q)).card := Finset.card_le_univ _
        _ = q ^ S.card := by
            rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
    · rw [min_eq_right h]
      exact le_trans (hrank_C S) hsing
  have hr : (0 : ℝ) < cutRank C S := by exact_mod_cast hrank_pos S
  calc cutEntropy C S ≤ Real.log (cutRank C S) := hent S
    _ ≤ Real.log ((q : ℝ) ^ (min S.card k)) :=
        Real.log_le_log hr (by exact_mod_cast hrank)
    _ = (min S.card k : ℕ) * Real.log q := Real.log_pow _ _
