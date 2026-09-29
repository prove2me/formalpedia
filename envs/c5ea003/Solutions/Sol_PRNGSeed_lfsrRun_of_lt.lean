-- Prove2me | solution 1 for PRNGSeed.lfsrRun_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T10:04:42.618207+00:00
-- url     : https://prove2.me/submissions/4e7ca422-13de-4a37-92fe-118fc8d2ddcd

/-
# `PRNGSeed.lfsrRun_of_lt`
Target `e2b26d76` (Open; re-read live immediately before submitting).

ORDINARY PROOF — screen CLEAN. Gift: **SAFE**.

BINDERS. History is `CE,CE,CE,CE`, so NO rejection has ever published an expected type here (a CE is
the submitter's own broken file). The telescope is therefore read off the bundle's variable lines,
taking only what the statement USES:
    line 48  variable {F : Type*} [CommRing F]      <- F and CommRing F: used by lfsrRun
    line 64  variable {L : ℕ} {c init : Fin L → F}  <- L, c, init: all three appear
giving `{F : Type*} [CommRing F] {L : ℕ} {c init : Fin L → F} {n : ℕ} (h : n < L)`.
The published statement leaves `L`, `c`, `init` unbound, which is what identifies them as section
variables rather than omissions.

DEFINITION (well-founded, note the `decreasing_by`):
    def lfsrRun {L : ℕ} (c init : Fin L → F) : ℕ → F
      | n => if h : n < L then init ⟨n, h⟩
             else ∑ i : Fin L, c i * lfsrRun c init (n - L + (i : ℕ))
      decreasing_by ... omega

MATHS. This is literally the first branch. With `h : n < L` the `dite` takes its positive arm.

PROBED, NOT GUESSED — and the probe overturned my reflex:
  * `lfsrRun` is defined by WELL-FOUNDED recursion, and Mathlib does NOT unfold such definitions with
    `rw [f]` / `unfold f` / `simp [f]`. Searching the whole library for `rw [Nat.log]`,
    `simp [Nat.log]` and `Nat.log.eq_def` returns NOTHING. Its own one-branch lemma
    `Nat.log_of_lt (hb : n < b) : log b n = 0` is proved with
        fun_cases log with | case1 => rfl | case2 => ...
    and `Nat.digits` likewise ships explicit `digits_def'` lemmas rather than unfolding at use sites.
    So `fun_cases` is the idiom here; `rw [lfsrRun]` was the habit that would have cost a compile.
  * `dif_pos {c : Prop} {h : Decidable c} (hc : c) {α} {t : c → α} {e : ¬c → α} : dite c t e = t hc`
    — Init/Core.lean:1195. `hc` is the only explicit argument.
-/
import Mathlib
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR

set_option autoImplicit false
set_option maxHeartbeats 400000

open PRNGSeed

open PRNGSeed in
/-- **The target, verbatim.** -/
theorem solution {F : Type*} [CommRing F] {L : ℕ} {c init : Fin L → F} {n : ℕ} (h : n < L) :
    lfsrRun c init n = init ⟨n, h⟩ := by
  rw [lfsrRun.eq_def]
  exact dif_pos h
