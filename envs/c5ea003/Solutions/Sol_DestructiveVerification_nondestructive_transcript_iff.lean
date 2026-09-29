-- Prove2me | solution 1 for DestructiveVerification.nondestructive_transcript_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:47:19.325741+00:00
-- url     : https://prove2.me/submissions/76b21cdc-503b-49cf-8ad6-c76984987ef1

-- Sol generated from Combinatorics/DestructiveVerificationRealization.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
import Definitions.Def_Combinatorics_DestructiveVerificationRealization
import Theorems.Thm_DestructiveVerification_transcript_eventually_periodic
import Theorems.Thm_DestructiveVerification_transcript_realization
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

/-- **State-complexity duality for destructive verification.**  A Boolean stream
is the transcript of a test on at most `n` dishes iff it is eventually periodic
with `preperiod + period ≤ n`.  The dish count needed to realise a verification
behaviour is exactly the combinatorial complexity of its verdict stream. -/
theorem transcript_characterization (u : ℕ → Bool) (n : ℕ) :
    (∃ (E : Type) (_ : Fintype E) (t : Test E) (d : E),
        Fintype.card E ≤ n ∧ ∀ m, transcript t d m = u m) ↔
      ∃ i p, 0 < p ∧ i + p ≤ n ∧ ∀ m, i ≤ m → u (m + p) = u m := by
  constructor
  · rintro ⟨E, hE, t, d, hcard, hu⟩
    obtain ⟨i, p, hp, hip, hper⟩ := transcript_eventually_periodic t d
    refine ⟨i, p, hp, by omega, fun m hm => ?_⟩
    rw [← hu, ← hu, hper m hm]
  · rintro ⟨i, p, hp, hip, hu⟩
    refine ⟨Fin (i + p), inferInstance, rhoTest i p hp u, ⟨0, by omega⟩, ?_, ?_⟩
    · simpa using hip
    · exact transcript_realization i p hp u hu





open DestructiveVerification in
theorem solution(u : ℕ → Bool) :
    (∃ (E : Type) (_ : Fintype E) (t : Test E) (d : E),
        Fintype.card E ≤ 1 ∧ ∀ m, transcript t d m = u m) ↔ ∀ m, u m = u 0 := by
  rw [transcript_characterization]
  constructor
  · rintro ⟨i, p, hp, hip, hper⟩
    have hi : i = 0 := by omega
    have hp1 : p = 1 := by omega
    subst hi; subst hp1
    intro m
    induction m with
    | zero => rfl
    | succ n ih => rw [← ih]; exact hper n (Nat.zero_le n)
  · intro h
    exact ⟨0, 1, one_pos, le_rfl, fun m _ => by rw [h (m + 1), h m]⟩
