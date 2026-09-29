-- Prove2me | solution 1 for RainbowAP.majority_rainbow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:36:41.779085+00:00
-- url     : https://prove2.me/submissions/c09704ba-6400-4378-900e-089e6bdcd8dc

-- Sol generated from Shared/RainbowAPRealization.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPRealization
import Definitions.Def_Shared_RainbowAPSpectrumMoments
import Definitions.Def_Shared_RainbowAPSpectrumThreshold
import Theorems.Thm_RainbowAP_majority_surjective_of
import Theorems.Thm_RainbowAP_missCount_eq_zero_iff

/-!
# From full spectra to genuine rainbow arithmetic progressions

The threshold studied in `Shared.RainbowAPSpectrumThreshold` is about words over an alphabet.
Here we give that alphabet its combinatorial meaning: the alphabet `Fin l → Fin k` is the set of
*colour patterns* of an `l`-term arithmetic progression coloured with `k` colours, and a word of
length `m` over it is exactly the restriction of a `k`-colouring of the interval `[0, l m)` to the
`m` consecutive `l`-term progressions of common difference `1`.

Main results.

* `RainbowAP.exists_rainbow_block` : a full-spectrum word contains an injective (rainbow) pattern
  as soon as `l ≤ k`.
* `RainbowAP.exists_rainbow_AP` : consequently, a `k`-colouring of `ℕ` whose block word on
  `[0, l m)` has full spectrum contains a genuine rainbow `l`-term arithmetic progression inside
  `[0, l m)`.
* `RainbowAP.majority_rainbow` : above the union-bound threshold, a strict majority of all
  patterns of length `m` already contain a rainbow progression.
* `RainbowAP.patternThreshold_bounds` : the `l`-pattern threshold is
  `Θ(k^l log(k^l))`; for `l = 2` this is the `Θ(k² log k)` regime of `Shared.RainbowAPPairThreshold`.
-/

open Finset

open RainbowAP

variable {k l m : ℕ}


/-- If there are at least as many colours as terms, a full-spectrum word contains a rainbow
(i.e. injectively coloured) block. -/
theorem exists_rainbow_block (hl : l ≤ k) (f : Fin m → (Fin l → Fin k))
    (hf : Function.Surjective f) : ∃ t : Fin m, Function.Injective (f t) := by
  set p : Fin l → Fin k := fun j => ⟨(j : ℕ), lt_of_lt_of_le j.isLt hl⟩ with hp
  have hpinj : Function.Injective p := by
    intro a b hab
    have h : ((p a : Fin k) : ℕ) = ((p b : Fin k) : ℕ) := congrArg Fin.val hab
    simp only [hp] at h
    exact Fin.ext h
  obtain ⟨t, ht⟩ := hf p
  exact ⟨t, ht ▸ hpinj⟩








open RainbowAP in
theorem solution(hl : l ≤ k)
    (h : 2 * Fintype.card (Fin l → Fin k) * (Fintype.card (Fin l → Fin k) - 1) ^ m
        < Fintype.card (Fin l → Fin k) ^ m) :
    Fintype.card (Fin l → Fin k) ^ m < 2 * (rainbowWords k l m).card := by
  have hmaj := majority_surjective_of (α := Fin l → Fin k) m h
  have hsub : nonSurjSet (Fin l → Fin k) m ∪ rainbowWords k l m = univ := by
    ext f
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hs : Function.Surjective f
    · exact Or.inr (by
        simp only [rainbowWords, Finset.mem_filter, Finset.mem_univ, true_and]
        exact exists_rainbow_block hl f hs)
    · refine Or.inl ?_
      simp only [nonSurjSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Nat.eq_zero_or_pos (missCount f) with h0 | hpos
      · exact absurd ((missCount_eq_zero_iff f).1 h0) hs
      · exact hpos
  have hcard : Fintype.card (Fin m → (Fin l → Fin k))
      ≤ nonSurjCount (Fin l → Fin k) m + (rainbowWords k l m).card := by
    have := Finset.card_union_le (nonSurjSet (Fin l → Fin k) m) (rainbowWords k l m)
    have h2 : (univ : Finset (Fin m → (Fin l → Fin k))).card
        ≤ nonSurjCount (Fin l → Fin k) m + (rainbowWords k l m).card := by
      rw [← hsub]
      exact this
    simpa [Finset.card_univ] using h2
  have hpow : Fintype.card (Fin m → (Fin l → Fin k)) = Fintype.card (Fin l → Fin k) ^ m := by
    simp
  rw [hpow] at hcard
  omega
