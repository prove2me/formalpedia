-- Prove2me | solution 1 for DestructiveVerification.exists_test_of_state_complexity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:47:16.295811+00:00
-- url     : https://prove2.me/submissions/2727ff20-d873-4ba5-8e57-3d885206018b

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
theorem solution(n : ℕ) (hn : 0 < n) :
    (∃ (E : Type) (_ : Fintype E) (t : Test E) (d : E),
        Fintype.card E ≤ n ∧ ∀ m, transcript t d m = periodicStream n m) ∧
      ¬ (∃ (E : Type) (_ : Fintype E) (t : Test E) (d : E),
        Fintype.card E ≤ n - 1 ∧ ∀ m, transcript t d m = periodicStream n m) := by
  constructor
  · rw [transcript_characterization]
    refine ⟨0, n, hn, by omega, fun m _ => ?_⟩
    simp only [periodicStream]
    congr 1
    simp [Nat.dvd_add_self_right]
  · rw [transcript_characterization]
    rintro ⟨i, p, hp, hip, hper⟩
    -- the stream is `false` exactly on multiples of `n`, so the period must be a
    -- multiple of `n`; but the hypothesis forces `p ≤ n - 1 < n`.
    have hM : i ≤ n * i := Nat.le_mul_of_pos_left i hn
    have hdvdM : n ∣ n * i := ⟨i, rfl⟩
    have h0 : periodicStream n (n * i) = false := by simp [periodicStream, hdvdM]
    have h1 : periodicStream n (n * i + p) = false := by rw [hper _ hM, h0]
    have hdvd : n ∣ n * i + p := by
      by_contra hcon
      simp [periodicStream, hcon] at h1
    have hnp : n ∣ p := (Nat.dvd_add_right hdvdM).mp hdvd
    have := Nat.le_of_dvd hp hnp
    omega
