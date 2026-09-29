-- Prove2me | solution 1 for dominationNumber_pathGraph
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T23:24:18.351167+00:00
-- url     : https://prove2.me/submissions/bff65fb2-e80c-4d5b-9a39-50e23bfa5434

import Mathlib
import Definitions.Def_Novelty_TransmissionDominationTree
open SimpleGraph in
theorem solution (n : ℕ) : dominationNumber (pathGraph n) = gammaPath n := by
  unfold dominationNumber gammaPath
  congr 1
  ext k
  simp only [Set.mem_setOf_eq]
  constructor
  · -- a dominating set of the path graph gives a dominating set of positions
    rintro ⟨D, hD, rfl⟩
    refine ⟨D.map Fin.valEmbedding, ⟨?_, ?_⟩, Finset.card_map _⟩
    · intro s hs
      obtain ⟨d, -, rfl⟩ := Finset.mem_map.mp hs
      exact Finset.mem_range.mpr d.isLt
    · intro i hi
      rw [Finset.mem_range] at hi
      rcases hD ⟨i, hi⟩ with h | ⟨d, hd, hadj⟩
      · exact ⟨i, Finset.mem_map.mpr ⟨⟨i, hi⟩, h, rfl⟩, by omega, by omega⟩
      · rw [pathGraph_adj] at hadj
        refine ⟨d.val, Finset.mem_map.mpr ⟨d, hd, rfl⟩, ?_, ?_⟩ <;> simp at hadj <;> omega
  · -- and conversely, reading positions as vertices of `Fin n`
    rintro ⟨S, ⟨hSr, hS⟩, rfl⟩
    refine ⟨Finset.univ.filter (fun v : Fin n => v.val ∈ S), ?_, ?_⟩
    · intro v
      obtain ⟨s, hs, h1, h2⟩ := hS v.val (Finset.mem_range.mpr v.isLt)
      have hsn : s < n := Finset.mem_range.mp (hSr hs)
      by_cases hsv : s = v.val
      · left
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hsv ▸ hs⟩
      · right
        refine ⟨⟨s, hsn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, ?_⟩
        rw [pathGraph_adj]
        simp only
        omega
    · have hmap : (Finset.univ.filter (fun v : Fin n => v.val ∈ S)).map Fin.valEmbedding = S := by
        ext s
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.valEmbedding_apply]
        constructor
        · rintro ⟨v, hv, rfl⟩
          exact hv
        · intro hs
          exact ⟨⟨s, Finset.mem_range.mp (hSr hs)⟩, hs, rfl⟩
      rw [← Finset.card_map Fin.valEmbedding, hmap]
