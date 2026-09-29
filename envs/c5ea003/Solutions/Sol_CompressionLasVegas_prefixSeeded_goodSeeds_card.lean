-- Prove2me | solution 1 for CompressionLasVegas.prefixSeeded_goodSeeds_card
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T22:10:34.909253+00:00
-- url     : https://prove2.me/submissions/ba61e0f1-8671-4cb3-86f7-91eccc0dcc56

import Definitions.Def_Speculative_AutoResearch_CompressionLasVegasOWF
open scoped Classical in
open CompressionOWF CompressionLasVegas in
theorem solution {i j s : ℕ} (y : Str) (hy : y.length = j + s) :
    2 ^ i ≤ (goodSeeds (prefixSeeded (j := j) (i := i)) s y).card := by
  let v : Fin j → Bool := fun t => y[(t : ℕ)]'(by omega)
  have hv : List.ofFn v = y.take j := by
    apply List.ext_getElem
    · simp
      omega
    · intro n h1 h2
      simp [v]
  have hsub : (Finset.univ.filter (fun r : (Fin j → Bool) × (Fin i → Bool) => r.1 = v))
      ⊆ goodSeeds (prefixSeeded (j := j) (i := i)) s y := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    simp only [goodSeeds, Finset.mem_filter, Finset.mem_univ, true_and]
    have hD : prefixSeeded r (y.drop j) = y := by
      unfold prefixSeeded
      rw [hr, hv, List.take_append_drop]
    refine ⟨⟨_, hD⟩, ?_⟩
    have hK : K (prefixSeeded r) y ≤ (y.drop j).length := Nat.sInf_le ⟨_, rfl, hD⟩
    simp only [List.length_drop, hy] at hK
    omega
  have hcard : (Finset.univ.filter (fun r : (Fin j → Bool) × (Fin i → Bool) => r.1 = v)).card = 2 ^ i := by
    have hset : Finset.univ.filter (fun r : (Fin j → Bool) × (Fin i → Bool) => r.1 = v)
        = ({v} : Finset (Fin j → Bool)) ×ˢ (Finset.univ : Finset (Fin i → Bool)) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        Finset.mem_singleton, and_true]
    rw [hset, Finset.card_product]
    simp
  calc 2 ^ i = (Finset.univ.filter (fun r : (Fin j → Bool) × (Fin i → Bool) => r.1 = v)).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub
