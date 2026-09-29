-- Prove2me | solution 2 for FactoringLab.adaptive_cov_eq_cov_bandMean
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T07:25:32.17789+00:00
-- url     : https://prove2.me/submissions/a4ab25fe-3b67-42c4-aa50-7da00228a5b8

import Mathlib
import Definitions.Def_Probability_AdaptiveBarrier
import Definitions.Def_Probability_StructuralOrthogonality
open FactoringLab Finset in
theorem solution {ι κ : Type*} [DecidableEq κ] (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ)
    (t : DTree ι) (ht : t.BandOnly Ω n) :
    cov Ω t.eval Y = cov Ω t.eval (bandMean Ω n Y) := by
  have key : ∀ g : κ → ℝ,
      ∑ i ∈ Ω, g (n i) * bandMean Ω n Y i = ∑ i ∈ Ω, g (n i) * Y i := by
    intro g
    have hmap : ∀ i ∈ Ω, n i ∈ Ω.image n := fun i hi => mem_image_of_mem n hi
    rw [← sum_fiberwise_of_maps_to hmap, ← sum_fiberwise_of_maps_to hmap]
    refine sum_congr rfl fun k hk => ?_
    have hband : ∀ i ∈ Ω.filter (fun i => n i = k), band Ω n i = Ω.filter (fun j => n j = k) := by
      intro i hi
      rw [mem_filter] at hi
      unfold band
      rw [hi.2]
    have hlhs : ∑ i ∈ Ω.filter (fun i => n i = k), g (n i) * bandMean Ω n Y i
        = ∑ _i ∈ Ω.filter (fun i => n i = k),
            g k * ((∑ j ∈ Ω.filter (fun j => n j = k), Y j) / (Ω.filter (fun j => n j = k)).card) := by
      refine sum_congr rfl fun i hi => ?_
      rw [bandMean, hband i hi, (mem_filter.mp hi).2]
    have hrhs : ∑ i ∈ Ω.filter (fun i => n i = k), g (n i) * Y i
        = ∑ i ∈ Ω.filter (fun i => n i = k), g k * Y i := by
      refine sum_congr rfl fun i hi => ?_
      rw [(mem_filter.mp hi).2]
    rw [hlhs, hrhs, sum_const, nsmul_eq_mul, ← mul_sum]
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hk
    have hne : ((Ω.filter (fun j => n j = n i)).card : ℝ) ≠ 0 := by
      have : 0 < (Ω.filter (fun j => n j = n i)).card :=
        card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, rfl⟩⟩
      exact_mod_cast this.ne'
    field_simp
  -- a band-only strategy computes a band-constant function ...
  have hT : ∀ s : DTree ι, s.BandOnly Ω n → ∀ i ∈ Ω, ∀ j ∈ Ω, n i = n j → s.eval i = s.eval j := by
    intro s
    induction s with
    | leaf v => intro hs; exact hs
    | node test l r ihl ihr =>
      intro hs i hi j hj hij
      obtain ⟨htest, hl, hr⟩ := hs
      simp only [DTree.eval]
      rw [htest i hi j hj hij]
      split_ifs
      · exact ihl hl i hi j hj hij
      · exact ihr hr i hi j hj hij
  -- ... i.e. a function of the band label on `Ω`
  obtain ⟨g, hg⟩ : ∃ g : κ → ℝ, ∀ i ∈ Ω, t.eval i = g (n i) := by
    classical
    refine ⟨fun k => if hk : ∃ i ∈ Ω, n i = k then t.eval hk.choose else 0, fun i hi => ?_⟩
    have hk : ∃ j ∈ Ω, n j = n i := ⟨i, hi, rfl⟩
    simp only [dif_pos hk]
    exact hT t ht i hi _ hk.choose_spec.1 hk.choose_spec.2.symm
  have h1 := key g
  have h2 : ∑ i ∈ Ω, bandMean Ω n Y i = ∑ i ∈ Ω, Y i := by simpa using key (fun _ => 1)
  have hcov : ∀ Z : ι → ℝ, cov Ω t.eval Z = cov Ω (fun i => g (n i)) Z := by
    intro Z
    have hs1 : ∑ i ∈ Ω, t.eval i * Z i = ∑ i ∈ Ω, g (n i) * Z i :=
      sum_congr rfl (fun i hi => by rw [hg i hi])
    have hs2 : ∑ i ∈ Ω, t.eval i = ∑ i ∈ Ω, g (n i) := sum_congr rfl (fun i hi => hg i hi)
    simp only [cov, FactoringLab.expect]
    rw [hs1, hs2]
  rw [hcov, hcov]
  simp only [cov, FactoringLab.expect]
  rw [h1, h2]
