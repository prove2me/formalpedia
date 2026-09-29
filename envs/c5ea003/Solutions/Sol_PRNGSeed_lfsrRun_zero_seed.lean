-- Prove2me | solution 1 for PRNGSeed.lfsrRun_zero_seed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T11:25:29.971993+00:00
-- url     : https://prove2.me/submissions/a9cebfae-24a8-4bfa-9a74-ebb535f47b12

/-
# `PRNGSeed.lfsrRun_zero_seed`
Target `e1bc49b4` (Open; re-read live immediately before submitting).

ORDINARY PROOF — screen CLEAN. Gift: currently GIFTS `e26c6137`, so this ships only AFTER that leaf
is Proved (an already-Proved conclusion cannot be gifted).

BINDERS — expected type from this target's OWN WA, verbatim:
    ∀ {F : Type} [CommRing F] {L : ℕ} (c : Fin L → F) (n : ℕ), lfsrRun c (fun x => 0) n = 0
`L` IMPLICIT here — unlike the sibling `lfsrRun_unitTap`, where `p` is an explicit binder of its own.
The two differ because `lfsrRun_unitTap` names its register length in the statement and this one does
not. Five submissions were rejected on type on each; carrying one sibling's list to the other is
exactly how that happens.

MATHS. A shift register seeded with zeros stays zero forever, whatever the taps: the first `L` outputs
are seed entries (all `0`), and every later output is a linear combination of earlier ones, hence `0`
by strong induction. Note the taps `c` are entirely arbitrary — nothing about them is used, which is
what makes this hold for every LFSR of length `L` at once.

This is also the key sub-lemma of `card_seedCompressible_le_sharp`: it is why the `2^L` pairs with
zero seed all produce the SAME word, collapsing to one, which is the "sharp" in that bound.

PROBED, NOT GUESSED:
  * `lfsrRun` is WELL-FOUNDED (`decreasing_by`); a four-candidate probe confirmed `rw [lfsrRun.eq_def]`
    works (as do `simp [lfsrRun]` and `unfold`).
  * `Nat.strong_induction_on` with case `| _ n ih` — the case NAME varies across Mathlib call sites
    (`ind`, `h`, `_`), so the anonymous form is used.
  * the `dif_pos` branch closes by `rw` alone: the seed is literally `fun _ => 0`, so the goal becomes
    `0 = 0` and `rw`'s own `rfl` finishes it. A trailing `simp` here would error "No goals to be
    solved" — that exact mistake cost two compiles earlier today.
-/
import Mathlib
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR

set_option autoImplicit false
set_option maxHeartbeats 400000

open PRNGSeed

open PRNGSeed in
/-- **The target, verbatim.** -/
theorem solution {F : Type*} [CommRing F] {L : ℕ} (c : Fin L → F) (n : ℕ) :
    lfsrRun c (fun _ => (0 : F)) n = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [lfsrRun.eq_def]
    by_cases h : n < L
    · rw [dif_pos h]
    · rw [dif_neg h]
      have hterm : ∀ i : Fin L, c i * lfsrRun c (fun _ => (0 : F)) (n - L + (i : ℕ)) = 0 := by
        intro i
        have hi := i.isLt
        have hlt : n - L + (i : ℕ) < n := by omega
        rw [ih _ hlt, mul_zero]
      simp [hterm]
