-- Prove2me | solution 1 for PRNGSeed.lfsrRun_unitTap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T10:56:57.796036+00:00
-- url     : https://prove2.me/submissions/62d26be2-1423-4461-a696-d0c0f7a67d69

/-
# `PRNGSeed.lfsrRun_unitTap`
Target `3f0acf92` (Open; re-read live immediately before submitting).

ORDINARY PROOF — screen CLEAN. Gift: currently GIFTS `53fb4727`, so this ships only AFTER that leaf
is Proved (already-Proved conclusions cannot be gifted).

BINDERS — expected type from this target's OWN WA, verbatim:
    ∀ {F : Type} [CommRing F] (p : ℕ) (hp : 0 < p) (init : Fin p → F) (n : ℕ),
      lfsrRun (unitTap p) init n = init ⟨n % p, ⋯⟩
Note `L` does NOT appear: `p` is its own explicit binder, shadowing the section's `variable {L}`.
Five submissions were rejected on type here; that is why.

MATHS. `unitTap p = fun i => if (i:ℕ) = 0 then 1 else 0`, so the feedback is just the symbol leaving
the register: it replays the seed with period `p`. Strong induction on the clock, splitting exactly
where `lfsrRun` splits.

PROBED, NOT GUESSED — all READ from source:
  * `lfsrRun` is WELL-FOUNDED (`decreasing_by`). A four-candidate probe showed `rw [lfsrRun.eq_def]`,
    `simp [lfsrRun, h]` and `unfold lfsrRun` ALL work; only my own malformed `fun_cases` branch failed.
    (I had previously written down that WF defs do not unfold with `rw` — that was Mathlib's house
    style, not a limit, and the probe overturned it.)
  * `Nat.mod_eq_of_lt {a b} (h : a < b) : a % b = a`              — core Init/Data/Nat/Div/Basic:178
  * `Nat.mod_eq_sub_mod {a b} (h : a ≥ b) : a % b = (a - b) % b`  — core Init/Data/Nat/Div/Basic:197
  * `Fin.val_inj {a b : Fin n} : a.1 = b.1 ↔ a = b` — CORE Init/Data/Fin/Basic:394, args
    IMPLICIT. `Fin.val_eq_val` (Mathlib Data/Fin/Basic:101) takes its Fin args EXPLICITLY, so
    `(Fin.val_eq_val _ _).mp` applied to a ℕ-equality has nothing to infer them from — that was
    an `Application type mismatch` here and in the periodic sibling. Mathlib's own idiom, at
    Data/Fin/Basic.lean:387, is exactly `Fin.val_inj.mp (Nat.mod_eq_of_lt h)`.
  * `Fin.val_mk (h : m < n) : (⟨m, h⟩ : Fin n).val = m := rfl` — CORE Init/Data/Fin/Lemmas:64
  * `Finset.sum_eq_single_of_mem (a) (h : a ∈ s) (h₀ : ∀ b ∈ s, b ≠ a → f b = 0) : ∑ x ∈ s, f x = f a`
    — the `to_additive` twin of `prod_eq_single_of_mem` (Basic.lean:337); it has NO source text, which
    is why a name-grep finds nothing; call sites prove it exists.
-/
import Mathlib
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR

set_option autoImplicit false
set_option maxHeartbeats 400000

open PRNGSeed

open PRNGSeed in
/-- **The target, verbatim.** -/
theorem solution {F : Type*} [CommRing F] (p : ℕ) (hp : 0 < p) (init : Fin p → F) (n : ℕ) :
    lfsrRun (unitTap p) init n = init ⟨n % p, Nat.mod_lt _ hp⟩ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [lfsrRun.eq_def]
    by_cases h : n < p
    · rw [dif_pos h]
      congr 1
      exact Fin.val_inj.mp (Nat.mod_eq_of_lt h).symm
    · rw [dif_neg h]
      have hge : n ≥ p := Nat.le_of_not_lt h
      -- every tap but the 0-th is zero, so the feedback sum collapses to one term
      have hzero : ∀ b ∈ (Finset.univ : Finset (Fin p)), b ≠ (⟨0, hp⟩ : Fin p) →
          unitTap p b * lfsrRun (unitTap p) init (n - p + (b : ℕ)) = 0 := by
        intro b _ hb
        have hbv : (b : ℕ) ≠ 0 := by
          intro hc
          exact hb (Fin.val_inj.mp (by simpa using hc))
        simp [unitTap, hbv]
      rw [Finset.sum_eq_single_of_mem (⟨0, hp⟩ : Fin p) (Finset.mem_univ _) hzero]
      have hlt : n - p < n := by omega
      have hidx : (n - p) % p = n % p := (Nat.mod_eq_sub_mod hge).symm
      -- `rw [hidx]` is a DEPENDENT rewrite (the Fin proof term's type depends on the value),
      -- failing with "motive is not type correct". `simp` handles the dependency. Probe-confirmed.
      simp [unitTap, ih (n - p) hlt, hidx]
