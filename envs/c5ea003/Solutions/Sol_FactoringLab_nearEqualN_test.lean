-- Prove2me | solution 1 for FactoringLab.nearEqualN_test
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T18:30:37.460143+00:00
-- url     : https://prove2.me/submissions/eefcc79c-3b23-4878-9bf0-ae74281f1e84

import Mathlib
import Definitions.Def_Probability_StructuralOrthogonality
open FactoringLab Finset in
theorem solution {ι κ : Type*} [DecidableEq κ] (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) (c : ℝ)
    (hconst : ∀ i ∈ Ω, bandMean Ω n Y i = c) (g : κ → ℝ) :
    cov Ω (fun i => g (n i)) Y = 0 := by
  -- tower property: on each fibre of `n`, `Y` sums to `c` times the fibre size
  have key : ∀ f : κ → ℝ, ∑ i ∈ Ω, f (n i) * Y i = c * ∑ i ∈ Ω, f (n i) := by
    intro f
    rw [← sum_fiberwise_of_maps_to (g := n) (t := Ω.image n) (fun i hi => mem_image_of_mem n hi),
      ← sum_fiberwise_of_maps_to (g := n) (t := Ω.image n) (fun i hi => mem_image_of_mem n hi),
      mul_sum]
    refine sum_congr rfl (fun k hk => ?_)
    obtain ⟨i0, hi0, rfl⟩ := mem_image.1 hk
    have hc := hconst i0 hi0
    unfold bandMean band at hc
    have hne : (Ω.filter (fun j => n j = n i0)).Nonempty := ⟨i0, mem_filter.2 ⟨hi0, rfl⟩⟩
    have hcard : (0 : ℝ) < ((Ω.filter (fun j => n j = n i0)).card : ℝ) :=
      Nat.cast_pos.2 (card_pos.2 hne)
    have hsum : ∑ j ∈ Ω.filter (fun j => n j = n i0), Y j
        = c * ((Ω.filter (fun j => n j = n i0)).card : ℝ) := by
      rw [← hc]
      field_simp
    have e1 : ∑ i ∈ Ω.filter (fun j => n j = n i0), f (n i) * Y i
        = f (n i0) * ∑ i ∈ Ω.filter (fun j => n j = n i0), Y i := by
      rw [mul_sum]
      exact sum_congr rfl (fun i hi => by rw [(mem_filter.1 hi).2])
    have e2 : ∑ i ∈ Ω.filter (fun j => n j = n i0), f (n i)
        = f (n i0) * ((Ω.filter (fun j => n j = n i0)).card : ℝ) := by
      rw [sum_congr rfl (fun i hi => by rw [(mem_filter.1 hi).2] : ∀ i ∈ Ω.filter
        (fun j => n j = n i0), f (n i) = f (n i0)), sum_const, nsmul_eq_mul]
      ring
    rw [e1, e2, hsum]
    ring
  have hY : ∑ i ∈ Ω, Y i = c * (Ω.card : ℝ) := by
    have := key (fun _ => 1)
    simp only [one_mul, sum_const, nsmul_eq_mul, mul_one] at this
    exact this
  unfold cov FactoringLab.expect
  rw [key g, hY]
  rcases Nat.eq_zero_or_pos Ω.card with h0 | hpos
  · simp [h0]
  · have hpos' : (0 : ℝ) < Ω.card := by exact_mod_cast hpos
    field_simp
    ring
