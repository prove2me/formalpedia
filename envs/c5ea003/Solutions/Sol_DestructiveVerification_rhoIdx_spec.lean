-- Prove2me | solution 1 for DestructiveVerification.rhoIdx_spec
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:43:29.830014+00:00
-- url     : https://prove2.me/submissions/2f6b09bc-07bc-4fae-9228-cb77da16cf44

-- Sol generated from Combinatorics/DestructiveVerificationRealization.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
import Definitions.Def_Combinatorics_DestructiveVerificationRealization
/-
# Destructive verification III: which verdict streams are realisable?

`Combinatorics.DestructiveVerificationDepth` shows that re-running a test on its
own residue produces a verdict stream — the *transcript* — that a finite dish
space cannot make arbitrarily wild.  This file pins down **exactly** which
streams occur.

Main results.

* `DestructiveVerification.transcript_eventually_periodic` — on `n` dishes every
  transcript is eventually periodic with preperiod `i` and period `p`
  satisfying `i + p ≤ n`.  (Analysis side.)
* `DestructiveVerification.transcript_realization` — conversely, *every*
  eventually periodic Boolean stream with preperiod `i` and period `p` is the
  transcript of an explicit test on exactly `i + p` dishes, the **rho test**
  whose residue map is the classical "rho" shape: a tail of length `i` feeding a
  cycle of length `p`.  (Synthesis side.)
* `DestructiveVerification.transcript_characterization` — the two combine into
  an exact characterisation: a stream is the transcript of a test on at most `n`
  dishes **iff** it is eventually periodic with `preperiod + period ≤ n`.  This
  is a state-complexity duality for destructive verification: the number of
  dishes needed to realise a verification behaviour is exactly the combinatorial
  complexity `i + p` of its verdict stream.
* `DestructiveVerification.nondestructive_transcript_iff` — the certificates sit
  exactly at the bottom of this scale: a test is nondestructive-like on a dish
  (constant transcript) iff its stream has period `1` and preperiod `0`, i.e.
  `i + p = 1`, the minimum possible.
* `DestructiveVerification.exists_test_of_state_complexity` — a strictness
  corollary: for each `n` there is a stream realisable on `n` dishes but on no
  fewer, so the dish-count hierarchy of verification behaviours is strict at
  every level.

Everything is proved from the orbit lemma of the previous file plus an explicit
combinatorial construction; no hardness assumption of any kind is used.
-/

open DestructiveVerification

variable {D : Type*}

/-! ## 1. Analysis: transcripts on `n` dishes are eventually periodic -/



/-! ## 2. Synthesis: the rho test -/


variable (i p : ℕ)




variable {i p}








/-! ## 3. The characterisation -/






open DestructiveVerification in
theorem solution(hp : 0 < p) (m : ℕ) :
    rhoIdx i p m < i + p ∧ ∃ c, m = rhoIdx i p m + c * p ∧
      (rhoIdx i p m = m ∨ i ≤ rhoIdx i p m) := by
  induction m with
  | zero =>
      refine ⟨by simp only [rhoIdx]; omega, 0, by simp [rhoIdx], Or.inl (by simp [rhoIdx])⟩
  | succ n ih =>
      obtain ⟨hlt, c, hc, hcase⟩ := ih
      by_cases hstep : rhoIdx i p n + 1 < i + p
      · refine ⟨by simp only [rhoIdx, if_pos hstep]; omega, c, ?_, ?_⟩
        · simp only [rhoIdx, if_pos hstep]; omega
        · simp only [rhoIdx, if_pos hstep]
          rcases hcase with h | h
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
      · refine ⟨by simp only [rhoIdx, if_neg hstep]; omega, c + 1, ?_, ?_⟩
        · simp only [rhoIdx, if_neg hstep]
          have hmul : (c + 1) * p = c * p + p := by ring
          omega
        · simp only [rhoIdx, if_neg hstep]
          exact Or.inr le_rfl
