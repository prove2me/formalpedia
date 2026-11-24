-- Prove2me | solution 1 for DigitalImmortality.Refined.few_small_codewords
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:23:28.70036+00:00
-- url     : https://prove2.me/submissions/d1fa7c87-fc9b-40ea-bc50-959427ba053c

import Mathlib
import Definitions.Def_Applications_NeuralCoding_MindEncodingRefined

/-!
# Incompressibility counting bound (pigeonhole)

Under any injective encoding of connectomes as natural numbers, at most `B`
connectomes are assigned a codeword whose numerical value is `< B`.

The proof is the direct pigeonhole: an injective map sends the set of
connectomes with codeword `< B` into the finite set `{0, …, B-1}`, so the
former has at most `B` elements.  No property of `Connectome` beyond the
fintype structure of `Fin (synapseSlots N) → Bool` is used.
-/

namespace DigitalImmortality.Refined

/-- Injective encodings into `ℕ` can give a codeword `< B` to at most `B`
connectomes. -/
theorem solution (N B : ℕ) {enc : Connectome N → ℕ}
    (hinj : Function.Injective enc) :
    (Finset.univ.filter (fun c : Connectome N => enc c < B)).card ≤ B := by
  classical
  have hsub : (Finset.univ.filter fun c : Connectome N => enc c < B).image enc ⊆
      Finset.range B := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hc).2
  calc (Finset.univ.filter fun c : Connectome N => enc c < B).card
      = ((Finset.univ.filter fun c : Connectome N => enc c < B).image enc).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (Finset.range B).card := Finset.card_le_card hsub
    _ = B := Finset.card_range B

end DigitalImmortality.Refined

open DigitalImmortality.Refined

/-- Injective encodings into `ℕ` can give a codeword `< B` to at most `B`
connectomes. -/
theorem solution (N B : ℕ) {enc : Connectome N → ℕ}
    (hinj : Function.Injective enc) :
    (Finset.univ.filter (fun c : Connectome N => enc c < B)).card ≤ B :=
  DigitalImmortality.Refined.solution N B hinj

#print axioms solution
