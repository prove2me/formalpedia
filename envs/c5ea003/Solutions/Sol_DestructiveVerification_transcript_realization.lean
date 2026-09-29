-- Prove2me | solution 1 for DestructiveVerification.transcript_realization
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:44:55.765421+00:00
-- url     : https://prove2.me/submissions/6f69332c-6eb9-4d48-aa81-2f698b8899df

-- Sol generated from Combinatorics/DestructiveVerificationRealization.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
import Definitions.Def_Combinatorics_DestructiveVerificationRealization
import Theorems.Thm_DestructiveVerification_rhoIdx_spec
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


lemma rhoMap_val (hp : 0 < p) (j : Fin (i + p)) :
    (rhoMap i p hp j).1 = if j.1 + 1 < i + p then j.1 + 1 else i := by
  unfold rhoMap
  split <;> rfl

/-- The orbit of dish `0` under the rho map is given by `rhoIdx`. -/
lemma rhoMap_iterate_val (hp : 0 < p) (m : ℕ) :
    (((rhoMap i p hp)^[m]) ⟨0, by omega⟩).1 = rhoIdx i p m := by
  induction m with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', rhoMap_val, ih]
      rfl


/-- Shifting an eventually periodic stream by a multiple of its period. -/
lemma stream_shift {u : ℕ → Bool} {i p : ℕ} (hu : ∀ m, i ≤ m → u (m + p) = u m) :
    ∀ c a, i ≤ a → u (a + c * p) = u a := by
  intro c
  induction c with
  | zero => intro a _; simp
  | succ c ih =>
      intro a ha
      have hmul : a + (c + 1) * p = (a + c * p) + p := by ring
      rw [hmul, hu _ (by omega), ih a ha]



/-! ## 3. The characterisation -/






open DestructiveVerification in
theorem solution(i p : ℕ) (hp : 0 < p) (u : ℕ → Bool)
    (hu : ∀ m, i ≤ m → u (m + p) = u m) :
    ∀ m, transcript (rhoTest i p hp u) ⟨0, by omega⟩ m = u m := by
  intro m
  have hres : residue (rhoTest i p hp u) = rhoMap i p hp := rfl
  have hval : (((residue (rhoTest i p hp u))^[m]) ⟨0, by omega⟩).1 = rhoIdx i p m := by
    rw [hres]; exact rhoMap_iterate_val hp m
  show u ((((residue (rhoTest i p hp u))^[m]) ⟨0, by omega⟩).1) = u m
  rw [hval]
  obtain ⟨_, c, hc, hcase⟩ := rhoIdx_spec (i := i) (p := p) hp m
  rcases hcase with h | h
  · rw [h]
  · conv_rhs => rw [hc]
    rw [stream_shift hu c _ h]
