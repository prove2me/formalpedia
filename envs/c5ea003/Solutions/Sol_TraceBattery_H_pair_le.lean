-- Prove2me | solution 1 for TraceBattery.H_pair_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T14:50:44.752798+00:00
-- url     : https://prove2.me/submissions/31caea55-cc4e-4513-8d4e-9839f18d7d2a

import Definitions.Def_Speculative_AutoResearch_TraceBatteryEntropy
open TraceBattery in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] {α β : Type*} (f : Ω → α) (g : Ω → β) :
    H (fun x => (f x, g x)) ≤ H f + H g := by
  classical
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  -- positivity of counts on attained readings
  have hposf : ∀ a ∈ img f, (0 : ℝ) < cnt f a := by
    intro a ha
    unfold img at ha
    rw [Finset.mem_image] at ha
    obtain ⟨z, _, rfl⟩ := ha
    unfold cnt fib
    exact_mod_cast Finset.card_pos.mpr ⟨z, by simp⟩
  have hposg : ∀ b ∈ img g, (0 : ℝ) < cnt g b := by
    intro b hb
    unfold img at hb
    rw [Finset.mem_image] at hb
    obtain ⟨z, _, rfl⟩ := hb
    unfold cnt fib
    exact_mod_cast Finset.card_pos.mpr ⟨z, by simp⟩
  have hposp : ∀ p ∈ img (fun x => (f x, g x)), (0 : ℝ) < cnt (fun x => (f x, g x)) p := by
    intro p hp
    simp only [img, Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨z, rfl⟩ := hp
    unfold cnt fib
    exact_mod_cast Finset.card_pos.mpr ⟨z, by simp⟩
  have hmem1 : ∀ p ∈ img (fun x => (f x, g x)), p.1 ∈ img f ∧ p.2 ∈ img g := by
    intro p hp
    simp only [img, Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨z, rfl⟩ := hp
    exact ⟨by simp [img], by simp [img]⟩
  -- total counts
  have htotf : ∑ c ∈ img (f), (cnt (f) c : ℝ) = Fintype.card Ω := by
    unfold cnt fib img
    rw [← Nat.cast_sum]
    congr 1
    rw [← Finset.card_univ]
    exact (Finset.card_eq_sum_card_image _ Finset.univ).symm
  have htotg : ∑ c ∈ img (g), (cnt (g) c : ℝ) = Fintype.card Ω := by
    unfold cnt fib img
    rw [← Nat.cast_sum]
    congr 1
    rw [← Finset.card_univ]
    exact (Finset.card_eq_sum_card_image _ Finset.univ).symm
  have htotp : ∑ c ∈ img (fun x => (f x, g x)), (cnt (fun x => (f x, g x)) c : ℝ) = Fintype.card Ω := by
    unfold cnt fib img
    rw [← Nat.cast_sum]
    congr 1
    rw [← Finset.card_univ]
    convert (Finset.card_eq_sum_card_image (fun x => (f x, g x)) Finset.univ).symm
  -- marginals as sums over attained pairs
  have hmargf : ∀ a, (cnt f a : ℝ)
      = ∑ p ∈ (img (fun x => (f x, g x))).filter (fun p => p.1 = a), (cnt (fun x => (f x, g x)) p : ℝ) := by
    intro a
    rw [← Nat.cast_sum]
    congr 1
    unfold cnt fib
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x => (f x, g x))
      (t := (img (fun x => (f x, g x))).filter (fun p => p.1 = a))]
    · refine Finset.sum_congr rfl (fun p hp => ?_)
      rw [Finset.mem_filter] at hp
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩
        exact h
      · intro h
        exact ⟨by rw [← hp.2, ← h], h⟩
    · intro z hz
      have hz' : f z = a := by simpa using hz
      exact Finset.mem_filter.mpr ⟨by simp only [img, Finset.mem_image, Finset.mem_univ, true_and]; exact ⟨z, rfl⟩, hz'⟩
  have hmargg : ∀ b, (cnt g b : ℝ)
      = ∑ p ∈ (img (fun x => (f x, g x))).filter (fun p => p.2 = b), (cnt (fun x => (f x, g x)) p : ℝ) := by
    intro b
    rw [← Nat.cast_sum]
    congr 1
    unfold cnt fib
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x => (f x, g x))
      (t := (img (fun x => (f x, g x))).filter (fun p => p.2 = b))]
    · refine Finset.sum_congr rfl (fun p hp => ?_)
      rw [Finset.mem_filter] at hp
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩
        exact h
      · intro h
        exact ⟨by rw [← hp.2, ← h], h⟩
    · intro z hz
      have hz' : g z = b := by simpa using hz
      exact Finset.mem_filter.mpr ⟨by simp only [img, Finset.mem_image, Finset.mem_univ, true_and]; exact ⟨z, rfl⟩, hz'⟩
  -- regroup H f and H g over attained pairs
  have hHf : H f = ∑ p ∈ img (fun x => (f x, g x)),
      ((cnt (fun x => (f x, g x)) p : ℝ) / Fintype.card Ω) * Real.log (Fintype.card Ω / cnt f p.1) := by
    unfold H
    rw [← Finset.sum_fiberwise_of_maps_to (s := img (fun x => (f x, g x))) (t := img f)
      (g := Prod.fst) (fun p hp => (hmem1 p hp).1)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hL : (cnt f a : ℝ) / Fintype.card Ω * Real.log (Fintype.card Ω / cnt f a)
        = (∑ p ∈ (img (fun x => (f x, g x))).filter (fun p => p.1 = a),
            (cnt (fun x => (f x, g x)) p : ℝ)) / Fintype.card Ω * Real.log (Fintype.card Ω / cnt f a) := by
      rw [← hmargf a]
    rw [hL, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [(Finset.mem_filter.mp hp).2]
  have hHg : H g = ∑ p ∈ img (fun x => (f x, g x)),
      ((cnt (fun x => (f x, g x)) p : ℝ) / Fintype.card Ω) * Real.log (Fintype.card Ω / cnt g p.2) := by
    unfold H
    rw [← Finset.sum_fiberwise_of_maps_to (s := img (fun x => (f x, g x))) (t := img g)
      (g := Prod.snd) (fun p hp => (hmem1 p hp).2)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have hL : (cnt g b : ℝ) / Fintype.card Ω * Real.log (Fintype.card Ω / cnt g b)
        = (∑ p ∈ (img (fun x => (f x, g x))).filter (fun p => p.2 = b),
            (cnt (fun x => (f x, g x)) p : ℝ)) / Fintype.card Ω * Real.log (Fintype.card Ω / cnt g b) := by
      rw [← hmargg b]
    rw [hL, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [(Finset.mem_filter.mp hp).2]
  -- pointwise Gibbs bound
  have hkey : ∀ p ∈ img (fun x => (f x, g x)),
      (cnt (fun x => (f x, g x)) p : ℝ) / Fintype.card Ω
          - (cnt f p.1 : ℝ) * cnt g p.2 / (Fintype.card Ω : ℝ) ^ 2
        ≤ (cnt (fun x => (f x, g x)) p : ℝ) / Fintype.card Ω
          * (Real.log (Fintype.card Ω / cnt f p.1) + Real.log (Fintype.card Ω / cnt g p.2)
            - Real.log (Fintype.card Ω / cnt (fun x => (f x, g x)) p)) := by
    intro p hp
    have hn := hposp p hp
    have ha := hposf p.1 (hmem1 p hp).1
    have hb := hposg p.2 (hmem1 p hp).2
    generalize (cnt (fun x => (f x, g x)) p : ℝ) = n at hn ⊢
    generalize (cnt f p.1 : ℝ) = na at ha ⊢
    generalize (cnt g p.2 : ℝ) = mb at hb ⊢
    generalize (Fintype.card Ω : ℝ) = N at hN ⊢
    have hNn : 0 < N / n := div_pos hN hn
    have hNa : 0 < N / na := div_pos hN ha
    have hNb : 0 < N / mb := div_pos hN hb
    have hrpos : 0 < (N / n) / ((N / na) * (N / mb)) := div_pos hNn (mul_pos hNa hNb)
    have hlog : Real.log ((N / n) / ((N / na) * (N / mb)))
        = Real.log (N / n) - (Real.log (N / na) + Real.log (N / mb)) := by
      rw [Real.log_div hNn.ne' (mul_pos hNa hNb).ne', Real.log_mul hNa.ne' hNb.ne']
    have h1 := Real.log_le_sub_one_of_pos hrpos
    rw [hlog] at h1
    have hr : (N / n) / ((N / na) * (N / mb)) = na * mb / (N * n) := by
      field_simp
    rw [hr] at h1
    have hu : 0 ≤ n / N := (div_pos hn hN).le
    have h2 := mul_le_mul_of_nonneg_left h1 hu
    have hsimp : n / N * (na * mb / (N * n) - 1) = na * mb / N ^ 2 - n / N := by
      field_simp
    rw [hsimp] at h2
    linarith
  -- the product marginals sum to at most one
  have hprod : ∑ p ∈ img (fun x => (f x, g x)), (cnt f p.1 : ℝ) * cnt g p.2 / (Fintype.card Ω : ℝ) ^ 2 ≤ 1 := by
    have hsub : img (fun x => (f x, g x)) ⊆ img f ×ˢ img g := fun p hp =>
      Finset.mem_product.mpr (hmem1 p hp)
    calc ∑ p ∈ img (fun x => (f x, g x)), (cnt f p.1 : ℝ) * cnt g p.2 / (Fintype.card Ω : ℝ) ^ 2
        ≤ ∑ p ∈ img f ×ˢ img g, (cnt f p.1 : ℝ) * cnt g p.2 / (Fintype.card Ω : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = (∑ a ∈ img f, (cnt f a : ℝ)) * (∑ b ∈ img g, (cnt g b : ℝ)) / (Fintype.card Ω : ℝ) ^ 2 := by
          rw [Finset.sum_product, Finset.sum_mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_div]
      _ = 1 := by
          rw [htotf, htotg]
          field_simp
  have hone : ∑ p ∈ img (fun x => (f x, g x)), (cnt (fun x => (f x, g x)) p : ℝ) / Fintype.card Ω = 1 := by
    rw [← Finset.sum_div, htotp, div_self hN.ne']
  have hsumkey := Finset.sum_le_sum hkey
  rw [Finset.sum_sub_distrib, hone] at hsumkey
  rw [hHf, hHg]
  unfold H
  have hexp : ∑ p ∈ img (fun x => (f x, g x)),
      (cnt (fun x => (f x, g x)) p : ℝ) / Fintype.card Ω
        * (Real.log (Fintype.card Ω / cnt f p.1) + Real.log (Fintype.card Ω / cnt g p.2)
          - Real.log (Fintype.card Ω / cnt (fun x => (f x, g x)) p))
      = (∑ p ∈ img (fun x => (f x, g x)),
          (cnt (fun x => (f x, g x)) p : ℝ) / Fintype.card Ω * Real.log (Fintype.card Ω / cnt f p.1))
        + (∑ p ∈ img (fun x => (f x, g x)),
          (cnt (fun x => (f x, g x)) p : ℝ) / Fintype.card Ω * Real.log (Fintype.card Ω / cnt g p.2))
        - ∑ p ∈ img (fun x => (f x, g x)),
          (cnt (fun x => (f x, g x)) p : ℝ) / Fintype.card Ω
            * Real.log (Fintype.card Ω / cnt (fun x => (f x, g x)) p) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  linarith
