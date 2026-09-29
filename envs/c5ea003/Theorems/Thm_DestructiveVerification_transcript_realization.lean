-- Prove2me | Theorems.Thm_DestructiveVerification_transcript_realization
-- name    : DestructiveVerification.transcript_realization
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:09:51.884896+00:00
-- url     : https://prove2.me/theorems/acaa9fd7-e96c-45b3-acba-a5ee5f98aed0
-- title:
--   Realisation.
-- statement:
--   **Realisation.**  Every Boolean stream that is periodic with period `p`
--   after step `i` is *exactly* the transcript of the rho test on `i + p` dishes.
--
--   ```lean
--   theorem DestructiveVerification.transcript_realization(i p : ℕ) (hp : 0 < p) (u : ℕ → Bool)
--       (hu : ∀ m, i ≤ m → u (m + p) = u m) :
--       ∀ m, transcript (rhoTest i p hp u) ⟨0, by omega⟩ m = u m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/DestructiveVerificationRealization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/DestructiveVerificationRealization.lean#L142

-- Thm stub generated from Combinatorics/DestructiveVerificationRealization.lean
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

theorem DestructiveVerification.transcript_realization(i p : ℕ) (hp : 0 < p) (u : ℕ → Bool)
    (hu : ∀ m, i ≤ m → u (m + p) = u m) :
    ∀ m, transcript (rhoTest i p hp u) ⟨0, by omega⟩ m = u m := by sorry
