-- Prove2me | solution 1 for RainbowAP.exists_rainbow_AP
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:31:12.408463+00:00
-- url     : https://prove2.me/submissions/4138215f-d468-4f69-954e-997e39dff751

-- Sol generated from Shared/RainbowAPRealization.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPRealization

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
theorem solution(hl : l ≤ k) (hl1 : 1 ≤ l) (chi : ℕ → Fin k)
    (hf : Function.Surjective (blockWord l m chi)) :
    ∃ a d : ℕ, 0 < d ∧ a + (l - 1) * d < l * m ∧
      Function.Injective (fun j : Fin l => chi (a + (j : ℕ) * d)) := by
  obtain ⟨t, ht⟩ := exists_rainbow_block hl _ hf
  refine ⟨l * (t : ℕ), 1, Nat.one_pos, ?_, ?_⟩
  · have h1 : (t : ℕ) + 1 ≤ m := t.isLt
    have h2 : l * ((t : ℕ) + 1) ≤ l * m := Nat.mul_le_mul_left l h1
    have h3 : l * (t : ℕ) + l ≤ l * m := by
      calc l * (t : ℕ) + l = l * ((t : ℕ) + 1) := by ring
        _ ≤ l * m := h2
    omega
  · intro a b hab
    simp only [mul_one] at hab
    exact ht (by simpa [blockWord] using hab)
