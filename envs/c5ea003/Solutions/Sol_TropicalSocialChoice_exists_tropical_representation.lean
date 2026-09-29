-- Prove2me | solution 1 for TropicalSocialChoice.exists_tropical_representation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T12:31:18.480525+00:00
-- url     : https://prove2.me/submissions/352ac8e2-1ded-41a2-adba-adaa85bb2ffd

import Mathlib
import Definitions.Def_Tropical_SocialChoice_TropicalArrow

open Finset TropicalSocialChoice in
theorem solution {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι] {F : (ι → ℝ) → ℝ}
    (h : IsTropAgg F) :
    ∃ (S : Finset ι) (hS : S.Nonempty) (δ : ι → ℝ),
      (∀ i ∈ S, 0 ≤ δ i) ∧ S.inf' hS δ = 0 ∧
      (∀ i, i ∈ S ↔ IsTropAgg.Active F i) ∧
      ∀ x, F x = S.inf' hS fun i => x i + δ i := by
  classical
  -- monotonicity
  have hmono : ∀ x y : ι → ℝ, (∀ j, x j ≤ y j) → F x ≤ F y := by
    intro x y hxy
    have e : (fun j => min (x j) (y j)) = x := funext fun j => min_eq_left (hxy j)
    have := h.min_hom x y
    rw [e] at this
    rw [this]
    exact min_le_right _ _
  have hconst : ∀ c : ℝ, F (fun _ => c) = c := by
    intro c
    have := h.trans_eq (fun _ => (0 : ℝ)) c
    simp only [zero_add] at this
    rw [this, h.norm, zero_add]
  set g : ι → ℝ → ℝ := fun i t => F (dip i t) with hg
  have hlow : ∀ i t, t ≤ 0 → t ≤ g i t := by
    intro i t ht
    have h1 := hmono (fun _ => t) (dip i t) (fun j => by
      simp only [dip]
      split_ifs <;> linarith)
    rw [hconst] at h1
    exact h1
  have hupp : ∀ i t, t ≤ 0 → g i t ≤ 0 := by
    intro i t ht
    have h1 := hmono (dip i t) (fun _ => 0) (fun j => by
      simp only [dip]
      split_ifs <;> linarith)
    rw [hconst] at h1
    exact h1
  have hsplit : ∀ i t M, t ≤ 0 → 0 ≤ M → g i t = min (g i (t - M) + M) 0 := by
    intro i t M ht hM
    have e : dip i t = fun j => min (dip i (t - M) j + M) ((fun _ => (0 : ℝ)) j) := by
      funext j
      simp only [dip]
      split_ifs
      · rw [sub_add_cancel, min_eq_left ht]
      · rw [zero_add, min_eq_right hM]
    simp only [hg]
    rw [e, h.min_hom, h.trans_eq, h.norm]
  -- min-homomorphism over a finite nonempty family
  have hinf : ∀ (s : Finset ι) (hs : s.Nonempty) (v : ι → ι → ℝ),
      F (fun j => s.inf' hs (fun i => v i j)) = s.inf' hs (fun i => F (v i)) := by
    intro s hs v
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a => simp
    | cons a s ha hs ih =>
      simp only [Finset.inf'_cons hs]
      exact (h.min_hom (v a) (fun j => s.inf' hs fun i => v i j)).trans
        (congrArg (min (F (v a))) ih)
  -- the shape of `g i` on active and inactive coordinates
  set δ : ι → ℝ := fun i =>
    if hact : IsTropAgg.Active F i then g i (Classical.choose hact) - Classical.choose hact else 0
    with hδ
  have hact_form : ∀ i, IsTropAgg.Active F i → ∀ t, t ≤ 0 → g i t = min 0 (t + δ i) := by
    intro i hact t ht
    obtain ⟨ht0, hg0⟩ := Classical.choose_spec hact
    set t0 := Classical.choose hact with ht0def
    have hδi : δ i = g i t0 - t0 := by
      simp only [hδ, dif_pos hact]
      rfl
    have hconst_h : ∀ s, s ≤ t0 → g i s - s = g i t0 - t0 := by
      intro s hs
      have := hsplit i t0 (t0 - s) ht0 (by linarith)
      rw [sub_sub_cancel] at this
      have hlt : g i t0 < 0 := hg0
      rcases min_cases (g i s + (t0 - s)) 0 with ⟨hm, -⟩ | ⟨hm, h2⟩
      · rw [hm] at this
        linarith
      · rw [hm] at this
        linarith
    have := hsplit i t (t - min t t0) ht (by linarith [min_le_left t t0])
    rw [show t - (t - min t t0) = min t t0 by ring] at this
    have hc := hconst_h (min t t0) (min_le_right t t0)
    rw [this, hδi, min_comm]
    congr 1
    linarith
  have hinact : ∀ i, ¬ IsTropAgg.Active F i → ∀ t, t ≤ 0 → g i t = 0 := by
    intro i hna t ht
    apply le_antisymm (hupp i t ht)
    by_contra hlt
    exact hna ⟨t, ht, not_le.1 hlt⟩
  -- representation with a large truncation level `M`
  have hrep : ∀ (x : ι → ℝ) (M : ℝ), (∀ j, x j ≤ M) →
      F x = univ.inf' univ_nonempty (fun i => g i (x i - M) + M) := by
    intro x M hM
    have e : x = fun j => univ.inf' univ_nonempty (fun i => dip i (x i - M) j + M) := by
      funext j
      apply le_antisymm
      · apply le_inf'
        intro i _
        simp only [dip]
        split_ifs with hij
        · rw [hij]
          linarith
        · linarith [hM j]
      · have h2 : dip j (x j - M) j + M = x j := by simp [dip]
        exact le_trans (inf'_le (fun i => dip i (x i - M) j + M) (mem_univ j)) (le_of_eq h2)
    conv_lhs => rw [e]
    rw [hinf]
    simp only [h.trans_eq, hg]
  set S : Finset ι := univ.filter (fun i => IsTropAgg.Active F i) with hSdef
  have hmemS : ∀ i, i ∈ S ↔ IsTropAgg.Active F i := by
    intro i
    simp [hSdef]
  have hSne : S.Nonempty := by
    by_contra hS
    have hall : ∀ i, ¬ IsTropAgg.Active F i := by
      intro i hi
      exact hS ⟨i, (hmemS i).2 hi⟩
    have h0 := hrep (fun _ => 0) 1 (fun _ => by norm_num)
    rw [h.norm] at h0
    have : univ.inf' univ_nonempty (fun i => g i ((fun _ : ι => (0 : ℝ)) i - 1) + 1) = 1 := by
      apply le_antisymm
      · obtain ⟨i0⟩ := ‹Nonempty ι›
        have := inf'_le (fun i => g i ((fun _ : ι => (0 : ℝ)) i - 1) + 1) (mem_univ i0)
        simp only at this
        rw [hinact i0 (hall i0) _ (by norm_num)] at this
        linarith
      · apply le_inf'
        intro i _
        simp only
        rw [hinact i (hall i) _ (by norm_num)]
        norm_num
    linarith
  -- the general formula
  have hform : ∀ x, F x = S.inf' hSne fun i => x i + δ i := by
    intro x
    set M := max (univ.sup' univ_nonempty x) (S.sup' hSne fun i => x i + δ i) with hMdef
    have hMx : ∀ j, x j ≤ M :=
      fun j => le_trans (le_sup' x (mem_univ j)) (le_max_left _ _)
    have hMd : ∀ i ∈ S, x i + δ i ≤ M :=
      fun i hi => le_trans (le_sup' (fun i => x i + δ i) hi) (le_max_right _ _)
    rw [hrep x M hMx]
    have hval : ∀ i, g i (x i - M) + M = if IsTropAgg.Active F i then x i + δ i else M := by
      intro i
      have hle : x i - M ≤ 0 := by linarith [hMx i]
      split_ifs with hact
      · rw [hact_form i hact _ hle]
        have := hMd i ((hmemS i).2 hact)
        rw [min_eq_right (by linarith)]
        ring
      · rw [hinact i hact _ hle, zero_add]
    apply le_antisymm
    · apply le_inf'
      intro i hi
      have := inf'_le (fun i => g i (x i - M) + M) (mem_univ i)
      rw [hval, if_pos ((hmemS i).1 hi)] at this
      exact this
    · apply le_inf'
      intro i _
      rw [hval]
      split_ifs with hact
      · exact inf'_le (fun i => x i + δ i) ((hmemS i).2 hact)
      · obtain ⟨i1, hi1⟩ := hSne
        exact le_trans (inf'_le (fun i => x i + δ i) hi1) (hMd i1 hi1)
  refine ⟨S, hSne, δ, ?_, ?_, hmemS, hform⟩
  · intro i hi
    have hact := (hmemS i).1 hi
    obtain ⟨ht0, -⟩ := Classical.choose_spec hact
    simp only [hδ, dif_pos hact]
    linarith [hlow i _ ht0]
  · have := hform (fun _ => 0)
    rw [h.norm] at this
    simp only [zero_add] at this
    exact this.symm
