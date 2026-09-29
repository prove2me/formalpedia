-- Prove2me | solution 1 for Catalog.Combinatorics.HybridEvictionAdditiveLaw.sum_lt_sum_of_sdiff_dominated
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T08:07:43.000614+00:00
-- url     : https://prove2.me/submissions/87ff7408-846c-49a1-a90a-9fdb63c4f20c

import Mathlib
import Definitions.Def_Combinatorics_HybridEvictionAdditiveLaw
open Catalog.Combinatorics.HybridEvictionAdditiveLaw Finset in
theorem solution {ι : Type*} [DecidableEq ι] (v : ι → ℝ) {S T : Finset ι}
    (hcard : T.card = S.card) (hne : T ≠ S)
    (hdom : ∀ j ∈ T \ S, ∀ i ∈ S \ T, v j < v i) :
    retained v T < retained v S := by
  -- split off the common part
  have hT : retained v T = ∑ i ∈ T \ S, v i + ∑ i ∈ T ∩ S, v i := by
    unfold retained
    rw [← sum_union (disjoint_sdiff_inter T S), sdiff_union_inter]
  have hS : retained v S = ∑ i ∈ S \ T, v i + ∑ i ∈ S ∩ T, v i := by
    unfold retained
    rw [← sum_union (disjoint_sdiff_inter S T), sdiff_union_inter]
  -- the two differences have the same size `k ≥ 1`
  have hk : (T \ S).card = (S \ T).card := by
    have h1 := card_sdiff_add_card_inter T S
    have h2 := card_sdiff_add_card_inter S T
    rw [inter_comm] at h2
    omega
  have hD : (T \ S).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    apply hne
    exact eq_of_subset_of_card_le (sdiff_eq_empty_iff_subset.mp h) (by omega)
  have hE : (S \ T).Nonempty := by
    rw [← card_pos, ← hk]
    exact card_pos.mpr hD
  -- every dropped value is below every kept one
  obtain ⟨j₀, hj₀, hjmax⟩ := exists_max_image (T \ S) v hD
  obtain ⟨i₀, hi₀, himin⟩ := exists_min_image (S \ T) v hE
  have hlt := hdom j₀ hj₀ i₀ hi₀
  have hup : ∑ i ∈ T \ S, v i ≤ (T \ S).card * v j₀ := by
    have := sum_le_card_nsmul (T \ S) v (v j₀) hjmax
    simpa [nsmul_eq_mul] using this
  have hlow : ((S \ T).card : ℝ) * v i₀ ≤ ∑ i ∈ S \ T, v i := by
    have := card_nsmul_le_sum (S \ T) v (v i₀) himin
    simpa [nsmul_eq_mul] using this
  have hkpos : (0 : ℝ) < (T \ S).card := by exact_mod_cast card_pos.mpr hD
  rw [hT, hS, inter_comm S T]
  rw [← hk] at hlow
  nlinarith
