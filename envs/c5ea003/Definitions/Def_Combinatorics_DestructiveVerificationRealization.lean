-- Prove2me | Definitions.Def_Combinatorics_DestructiveVerificationRealization
-- name    : Combinatorics_DestructiveVerificationRealization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:33:13.432986+00:00
-- url     : https://prove2.me/theorems/44c9fbca-502d-4cd1-b5c1-a35618c5b223
-- title:
--   Aether Catalog definitions — Combinatorics_DestructiveVerificationRealization
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.DestructiveVerificationRealization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/DestructiveVerificationRealization.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
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

namespace DestructiveVerification

variable {D : Type*}

/-! ## 1. Analysis: transcripts on `n` dishes are eventually periodic -/



/-! ## 2. Synthesis: the rho test -/

section Rho

variable (i p : ℕ)

/-- The **rho map** on `i + p` dishes: a tail `0 → 1 → ⋯ → i + p - 1` that feeds
back into position `i`, creating a cycle of length `p` after a transient of
length `i`. -/
def rhoMap (hp : 0 < p) : Fin (i + p) → Fin (i + p) :=
  fun j => if h : j.1 + 1 < i + p then ⟨j.1 + 1, h⟩ else ⟨i, by omega⟩

/-- The index reached after `m` runs of the rho map, described by the same
recursion. -/
def rhoIdx : ℕ → ℕ
  | 0 => 0
  | m + 1 => if rhoIdx m + 1 < i + p then rhoIdx m + 1 else i

/-- The **rho test** for a Boolean stream `u`: the dish advances along the rho
shape and the verdict reads off `u` at the current position. -/
def rhoTest (hp : 0 < p) (u : ℕ → Bool) : Test (Fin (i + p)) :=
  fun j => (u j.1, rhoMap i p hp j)

variable {i p}







end Rho

/-! ## 3. The characterisation -/



/-- The stream that says `false` exactly at the multiples of `n`, otherwise
`true`; its complexity is exactly `n`. -/
def periodicStream (n : ℕ) : ℕ → Bool := fun m => decide ¬ (n ∣ m)


end DestructiveVerification


