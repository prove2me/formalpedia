-- Prove2me | solution 1 for CutIndexedSingleton.cutRank_eq_pow_of_isMDS
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T04:29:16.902998+00:00
-- url     : https://prove2.me/submissions/0241f39b-ce5b-44e6-99f8-1ca09d5f9eed

import Mathlib
import Definitions.Def_Novelty_CutIndexedSingleton

open Finset CutIndexedSingleton in
theorem solution {n q : ℕ} {C : Finset (Word n q)} {d : ℕ} (hmds : IsMDS C d)
    (hd1 : 1 ≤ d) (hq : 0 < q) {S : Finset (Fin n)} (hS : S.card ≤ CutData.sdim n d) :
    cutRank C S = q ^ S.card := by
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
  unfold cutRank
  have himg : C.image (proj S) = univ := by
    apply Finset.eq_univ_of_forall
    intro y
    have h := hfib S hS y
    have hpos : 0 < (fiber C S y).card := by
      rw [h]
      exact pow_pos hq _
    obtain ⟨c, hc⟩ := Finset.card_pos.1 hpos
    rw [fiber, Finset.mem_filter] at hc
    exact Finset.mem_image.2 ⟨c, hc.1, hc.2⟩
  rw [himg, Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
