-- Prove2me | solution 1 for Catalog.Probability.SeedRec.unique_decoding_of_long_window
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:34:44.777409+00:00
-- url     : https://prove2.me/submissions/3446c511-ca3e-4d3f-934c-33d0ceb22c7f

-- Sol generated from Probability/PRNGNoiseTolerance.lean
import Mathlib
import Definitions.Def_Probability_PRNGBerlekampMassey
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGNoiseTolerance
import Theorems.Thm_Catalog_Probability_SeedRec_exists_error_free_block
import Theorems.Thm_Catalog_Probability_SeedRec_lfsr_seq_determined_by_two_L

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

omit [CommRing K] in
theorem eq_of_not_mem_errorSet {w : Fin n → K} {y : ℕ → K} {i : Fin n}
    (h : i ∉ errorSet w y) : w i = y (i : ℕ) := by
  simpa using h


/-! ## The refutation of C4 -/









/-! ### Sharpness of the corrected threshold at order one -/







/-! ## The corrected threshold -/


/-- `SatisfiesLFSR` is shift invariant. -/
theorem satisfiesLFSR_shift {c : Fin L → K} {y : ℕ → K} (hy : SatisfiesLFSR c y) (j : ℕ) :
    SatisfiesLFSR c (fun t => y (j + t)) := by
  intro t
  have h := hy (j + t)
  simpa [Nat.add_assoc] using h

variable [Nontrivial K]

/-- **Shifted `2L` theorem.**  Two streams of linear complexity `≤ L` that agree
on *some* `2L` consecutive indices agree from that point onwards. -/
theorem lfsr_seq_determined_of_block (c c' : Fin L → K) (y z : ℕ → K)
    (hy : SatisfiesLFSR c y) (hz : SatisfiesLFSR c' z) (j : ℕ)
    (hagree : ∀ t, j ≤ t → t < j + 2 * L → y t = z t) :
    ∀ t, j ≤ t → y t = z t := by
  have hy' : SatisfiesLFSR c (fun t => y (j + t)) := satisfiesLFSR_shift hy j
  have hz' : SatisfiesLFSR c' (fun t => z (j + t)) := satisfiesLFSR_shift hz j
  have hag : ∀ t < 2 * L, y (j + t) = z (j + t) := fun t ht =>
    hagree (j + t) (by omega) (by omega)
  have heq := lfsr_seq_determined_by_two_L c c' _ _ hy' hz' hag
  intro t ht
  have h := congrFun heq (t - j)
  simpa [Nat.add_sub_cancel' ht] using h


variable [DecidableEq K]




open Catalog.Probability.SeedRec in
theorem solution(c c' : Fin L → K) (y z : ℕ → K)
    (hy : SatisfiesLFSR c y) (hz : SatisfiesLFSR c' z) (w : Fin n → K) (e : ℕ)
    (hwy : (errorSet w y).card ≤ e) (hwz : (errorSet w z).card ≤ e)
    (hn : 2 * L * (2 * e + 1) ≤ n) :
    ∃ j, j + 2 * L ≤ n ∧ ∀ t, j ≤ t → y t = z t := by
  classical
  have hcard : (errorSet w y ∪ errorSet w z).card ≤ 2 * e :=
    (Finset.card_union_le _ _).trans (by omega)
  obtain ⟨m, hm, hblock⟩ := exists_error_free_block (errorSet w y ∪ errorSet w z) e hcard
  have hmono : 2 * L * (m + 1) ≤ 2 * L * (2 * e + 1) := Nat.mul_le_mul_left _ (by omega)
  have hexp : 2 * L * (m + 1) = 2 * L * m + 2 * L := by ring
  refine ⟨2 * L * m, by omega, ?_⟩
  refine lfsr_seq_determined_of_block c c' y z hy hz (2 * L * m) ?_
  intro t ht1 ht2
  have htn : t < n := by omega
  have hnot := hblock ⟨t, htn⟩ (by simpa using ht1) (by simpa using ht2)
  rw [Finset.mem_union] at hnot
  push_neg at hnot
  have h1 : w ⟨t, htn⟩ = y t := eq_of_not_mem_errorSet hnot.1
  have h2 : w ⟨t, htn⟩ = z t := eq_of_not_mem_errorSet hnot.2
  rw [← h1, h2]
