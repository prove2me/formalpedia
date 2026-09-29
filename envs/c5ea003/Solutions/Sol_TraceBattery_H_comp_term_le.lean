-- Prove2me | solution 1 for TraceBattery.H_comp_term_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T14:42:28.471583+00:00
-- url     : https://prove2.me/submissions/ef854031-a333-4290-bf54-543770b449eb

import Definitions.Def_Speculative_AutoResearch_TraceBatteryEntropy
open Classical in
open TraceBattery in
theorem solution {Ω : Type*} [Fintype Ω] {α : Type*} {β : Type*} [Nonempty Ω] (f : Ω → α)
    (g : α → β) {b : β} (hb : b ∈ img (g ∘ f)) :
    ((cnt (g ∘ f) b : ℝ) / (Fintype.card Ω : ℝ))
        * Real.log ((Fintype.card Ω : ℝ) / cnt (g ∘ f) b)
      ≤ ∑ a ∈ (img f).filter (fun a => g a = b),
          ((cnt f a : ℝ) / (Fintype.card Ω : ℝ)) * Real.log ((Fintype.card Ω : ℝ) / cnt f a) := by
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
  exact hterm b hb
