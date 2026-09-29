-- Prove2me | solution 1 for TraceBattery.H_comp_lt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T14:38:15.746699+00:00
-- url     : https://prove2.me/submissions/a27ac511-f9fa-4250-9600-a5ed047d4f02

import Definitions.Def_Speculative_AutoResearch_TraceBatteryEntropy
open TraceBattery in
theorem solution {Ω : Type*} [Fintype Ω] {α : Type*} {β : Type*} [Nonempty Ω] (f : Ω → α)
    (g : α → β) {x y : Ω} (hcoarse : g (f x) = g (f y)) (hfine : f x ≠ f y) :
    H (g ∘ f) < H f := by
  classical
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hcpos : ∀ a ∈ img f, (0 : ℝ) < cnt f a := by
    intro a ha
    unfold img at ha
    rw [Finset.mem_image] at ha
    obtain ⟨z, _, rfl⟩ := ha
    unfold cnt fib
    exact_mod_cast Finset.card_pos.mpr ⟨z, by simp⟩
  have hgroup : ∀ b, (cnt (g ∘ f) b : ℝ)
      = ∑ a ∈ (img f).filter (fun a => g a = b), (cnt f a : ℝ) := by
    intro b
    rw [← Nat.cast_sum]
    congr 1
    unfold cnt fib
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := (img f).filter (fun a => g a = b))]
    · refine Finset.sum_congr rfl (fun a ha => ?_)
      rw [Finset.mem_filter] at ha
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
      constructor
      · rintro ⟨_, h⟩
        exact h
      · intro h
        exact ⟨by rw [h]; exact ha.2, h⟩
    · intro z hz
      have hz' : g (f z) = b := by simpa [Function.comp] using hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem f (Finset.mem_univ z), hz'⟩
  have hterm : ∀ b ∈ img (g ∘ f),
      ((cnt (g ∘ f) b : ℝ) / (Fintype.card Ω : ℝ)) * Real.log ((Fintype.card Ω : ℝ) / cnt (g ∘ f) b)
        ≤ ∑ a ∈ (img f).filter (fun a => g a = b),
          ((cnt f a : ℝ) / (Fintype.card Ω : ℝ)) * Real.log ((Fintype.card Ω : ℝ) / cnt f a) := by
    intro b _
    rw [hgroup b, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_le_sum (fun a ha => ?_)
    have ha' := Finset.mem_filter.mp ha
    have hca := hcpos a ha'.1
    have hle : (cnt f a : ℝ) ≤ ∑ a' ∈ (img f).filter (fun a => g a = b), (cnt f a' : ℝ) :=
      Finset.single_le_sum (f := fun a' => (cnt f a' : ℝ)) (fun _ _ => Nat.cast_nonneg _) ha
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hca.le hN.le)
    apply Real.log_le_log (div_pos hN (lt_of_lt_of_le hca hle))
    exact div_le_div_of_nonneg_left hN.le hca hle
  have hfx : f x ∈ img f := by simp [img]
  have hfy : f y ∈ img f := by simp [img]
  have hb0 : g (f x) ∈ img (g ∘ f) := by simp [img]
  have hstrict :
      ((cnt (g ∘ f) (g (f x)) : ℝ) / (Fintype.card Ω : ℝ))
          * Real.log ((Fintype.card Ω : ℝ) / cnt (g ∘ f) (g (f x)))
        < ∑ a ∈ (img f).filter (fun a => g a = g (f x)),
          ((cnt f a : ℝ) / (Fintype.card Ω : ℝ)) * Real.log ((Fintype.card Ω : ℝ) / cnt f a) := by
    rw [hgroup (g (f x)), Finset.sum_div, Finset.sum_mul]
    apply Finset.sum_lt_sum
    · intro a ha
      have ha' := Finset.mem_filter.mp ha
      have hca := hcpos a ha'.1
      have hle : (cnt f a : ℝ) ≤ ∑ a' ∈ (img f).filter (fun a => g a = g (f x)), (cnt f a' : ℝ) :=
        Finset.single_le_sum (f := fun a' => (cnt f a' : ℝ)) (fun _ _ => Nat.cast_nonneg _) ha
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hca.le hN.le)
      apply Real.log_le_log (div_pos hN (lt_of_lt_of_le hca hle))
      exact div_le_div_of_nonneg_left hN.le hca hle
    · have hmemx : f x ∈ (img f).filter (fun a => g a = g (f x)) :=
        Finset.mem_filter.mpr ⟨hfx, rfl⟩
      have hmemy : f y ∈ (img f).filter (fun a => g a = g (f x)) :=
        Finset.mem_filter.mpr ⟨hfy, hcoarse.symm⟩
      refine ⟨f x, hmemx, ?_⟩
      have hca := hcpos (f x) hfx
      have hcb := hcpos (f y) hfy
      have hsub : ({f x, f y} : Finset α) ⊆ (img f).filter (fun a => g a = g (f x)) := by
        intro a ha
        rw [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact hmemx
        · exact hmemy
      have hpair := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (f := fun a' => (cnt f a' : ℝ)) (fun _ _ _ => Nat.cast_nonneg _)
      rw [Finset.sum_pair hfine] at hpair
      have hlt : (cnt f (f x) : ℝ) < ∑ a' ∈ (img f).filter (fun a => g a = g (f x)), (cnt f a' : ℝ) := by
        linarith
      apply mul_lt_mul_of_pos_left _ (div_pos hca hN)
      apply Real.log_lt_log (div_pos hN (by linarith))
      exact div_lt_div_of_pos_left hN hca hlt
  have hmaps : ∀ a ∈ img f, g a ∈ img (g ∘ f) := by
    intro a ha
    simp only [img, Finset.mem_image, Finset.mem_univ, true_and] at ha ⊢
    obtain ⟨z, rfl⟩ := ha
    exact ⟨z, rfl⟩
  unfold H
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  exact Finset.sum_lt_sum (fun b hb => hterm b hb) ⟨g (f x), hb0, hstrict⟩
