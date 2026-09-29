-- Prove2me | solution 1 for Catalog.Probability.SeedRec.card_errorSet_sharpWord_alt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:04:47.39214+00:00
-- url     : https://prove2.me/submissions/d7752acd-26be-4fe4-b6d0-66a570bce747

-- Sol generated from Probability/PRNGNoiseTolerance.lean
import Mathlib
import Definitions.Def_Probability_PRNGBerlekampMassey
import Definitions.Def_Probability_PRNGNoiseTolerance

/-!
# Noise-tolerant fingerprinting: the `2L + 2e + 1` conjecture is false

Real files are only *nearly* PRNG output (headers, checksums, interleaved
metadata), so the seed-compression router needs a fingerprint test that
tolerates `e` corrupted symbols.  Conjecture **C4** of `FUTURE_DIRECTIONS.md`
proposed the Reed–Solomon-style bound: a window of length `n ≥ 2L + 2e + 1`
should determine the underlying order-`L` stream uniquely.

This file settles C4 **negatively** and repairs it.

* `errorSet` — the corrupted positions of an observed word relative to a
  candidate stream.
* `noise_tolerance_two_L_plus_two_e_false` — **C4 is false**, for every error
  budget `e ≥ 1`: over `ZMod 3` there are two *distinct* order-one streams and
  a word of length exactly `2·1 + 2e + 1` lying within Hamming distance `e` of
  both.  The counterexample is structural, not accidental: the two streams
  agree on every even index, so their disagreements are spread out and no
  window of length `2L` is error-free — precisely the failure mode flagged as
  the caveat when C4 was stated.
* `noise_tolerance_five_false` — the smallest instance (`e = 1`, `n = 5`).
* `lfsr_seq_determined_of_block` — the shifted `2L` theorem: agreement on *any*
  `2L` consecutive indices forces agreement from there on.
* `exists_error_free_block` — a pigeonhole: `2e` errors cannot meet all of the
  `2e + 1` disjoint blocks of length `2L`.
* `unique_decoding_of_long_window` — **corrected conjecture C4′**: window length
  `2L(2e + 1)` *does* suffice.  Two order-`L` streams within distance `e` of a
  common observed word agree from some index `j` with `j + 2L ≤ n` onwards.
* `unique_decoding_threshold_sharp_order_one` — the corrected threshold is
  **sharp** at `L = 1`: unique decoding still fails at length
  `4e + 1 = 2·1·(2e + 1) - 1`, one symbol short of it.

Together the results pin the truth at order one: the correct threshold for
noise-tolerant LFSR fingerprinting is *not* the linear `2L + 2e + 1` but exactly
the multiplicative `2L(2e + 1)`.
-/

open Catalog.Probability.SeedRec

open Finset

variable {K : Type*} [CommRing K] {L n : ℕ}


variable [DecidableEq K]


omit [CommRing K] in
@[simp] theorem mem_errorSet {w : Fin n → K} {y : ℕ → K} {i : Fin n} :
    i ∈ errorSet w y ↔ w i ≠ y (i : ℕ) := by
  simp [errorSet]



/-! ## The refutation of C4 -/




/-- In `ZMod 3` the powers of `2 = -1` alternate. -/
theorem two_pow_zmod_three (t : ℕ) : (2 : ZMod 3) ^ t = if Even t then 1 else 2 := by
  have h2 : (2 : ZMod 3) = -1 := by decide
  rcases Nat.even_or_odd t with ht | ht
  · rw [h2, ht.neg_one_pow, if_pos ht]
  · rw [h2, ht.neg_one_pow, if_neg (Nat.not_even_iff_odd.mpr ht)]





/-! ### Sharpness of the corrected threshold at order one -/







/-! ## The corrected threshold -/



variable [Nontrivial K]



variable [DecidableEq K]




open Catalog.Probability.SeedRec in
theorem solution(e : ℕ) :
    (errorSet (sharpWord e) (fun t => (2 : ZMod 3) ^ t)).card ≤ e := by
  classical
  have hchar : ∀ i ∈ errorSet (sharpWord e) (fun t => (2 : ZMod 3) ^ t),
      (i : ℕ) % 2 = 1 ∧ (i : ℕ) < 2 * e := by
    intro i hi
    rw [mem_errorSet] at hi
    simp only [sharpWord, two_pow_zmod_three] at hi
    by_cases h0 : (i : ℕ) % 2 = 0
    · refine absurd ?_ hi
      rw [if_pos h0, if_pos (Nat.even_iff.mpr h0)]
    · have hnotEven : ¬ Even (i : ℕ) := by rw [Nat.even_iff]; exact h0
      rw [if_neg hnotEven, if_neg h0] at hi
      by_cases h1 : (i : ℕ) < 2 * e
      · exact ⟨by omega, h1⟩
      · exact absurd (by rw [if_neg h1]) hi
  calc (errorSet (sharpWord e) (fun t => (2 : ZMod 3) ^ t)).card
      ≤ (Finset.range e).card := by
        refine Finset.card_le_card_of_injOn (fun i => ((i : ℕ) - 1) / 2) ?_ ?_
        · intro i hi
          obtain ⟨hp, h2⟩ := hchar i (by simpa using hi)
          have hgoal : ((i : ℕ) - 1) / 2 < e := by omega
          simpa using hgoal
        · intro i hi j hj hij
          obtain ⟨hp, h2⟩ := hchar i (by simpa using hi)
          obtain ⟨hp', h2'⟩ := hchar j (by simpa using hj)
          simp only at hij
          exact Fin.ext (by omega)
    _ = e := Finset.card_range e
