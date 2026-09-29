-- Prove2me | solution 1 for DestructiveVerification.exists_idempotent_iterate
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:41:37.923093+00:00
-- url     : https://prove2.me/submissions/11b4ab51-556f-4f11-8f4d-52a302400f2c

-- Sol generated from Combinatorics/DestructiveVerificationDepth.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
/-
# Destructive verification II: transcripts, destruction depth, and stabilisation

Companion to `Combinatorics.DestructiveVerification`, which sets up a test as a
state transition `t : D → Bool × D` returning a verdict and a residual dish.
Here we study what happens when a test is **re-run on its own residue**, i.e.
the *transcript*

  `transcript t d k = verdict t ((residue t)^[k] d)`,

the verdict stream produced by running the same test over and over on the
successive residues of a single dish.

The results answer three questions that the one-shot picture cannot even ask.

* **How long can a destructive test masquerade as a certificate?**
  `DestructiveVerification.transcript_rigid`: on a dish type with `n` dishes, a
  transcript that is constant on its first `n` entries is constant forever.
  So the "destruction depth" of a test — the first index at which the verdict
  changes — is either infinite or `< n`.
* **Is that bound sharp?**  `DestructiveVerification.depth_hierarchy` builds,
  for every `k`, a test on `k + 2` dishes whose transcript is constant on
  `[0, k]` and flips at `k + 1 = n - 1`.  Together with rigidity this gives a
  *strict, exhaustive hierarchy of destruction depths*
  (`DestructiveVerification.depth_hierarchy_sharp`): every value `< n` is
  realised and no value `≥ n` is.
* **Does repeated testing ever settle down?**
  `DestructiveVerification.exists_idempotent_iterate` and
  `DestructiveVerification.batch_residue_idempotent`: on a finite dish type
  there is a batch length `N > 0` such that running the batch twice leaves the
  same dish as running it once — every test is nondestructive on its own
  stabilised residue.

The capstone is `DestructiveVerification.batch_accept_forever`: a dish that
survives `n = #D` consecutive runs of a test survives *arbitrarily many* runs.
Finite testing certifies infinite testing — but only after `n` runs, and
`depth_hierarchy` shows `n - 1` runs are genuinely not enough.

The engine behind all of this is the orbit lemma
`DestructiveVerification.exists_orbit_rep`: every point of the forward orbit of
a dish under the residue map is already one of the first `n` points of that
orbit.
-/

open DestructiveVerification

variable {D : Type*}

/-! ## 1. Transcripts -/







/-! ## 2. The orbit lemma -/



/-! ## 3. Rigidity: destruction depth is either infinite or `< #D` -/



/-! ## 4. Sharpness: a test of every destruction depth -/






/-! ## 5. Batches: running a test `n` times in a row -/







/-! ## 6. Stabilisation: every test is nondestructive on its own core -/






open DestructiveVerification in
theorem solution[Finite D] (f : D → D) :
    ∃ N, 0 < N ∧ ∀ d, f^[N] (f^[N] d) = f^[N] d := by
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n])
  -- normalise so that `i < j`
  obtain ⟨i, j, hij, hfij⟩ : ∃ i j, i < j ∧ f^[i] = f^[j] := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b, h, hfab⟩
    · exact ⟨b, a, h, hfab.symm⟩
  set p := j - i with hp
  have hp0 : 0 < p := by omega
  have hstep : ∀ m, i ≤ m → ∀ d, f^[m + p] d = f^[m] d := by
    intro m hm d
    have h1 : m + p = (m - i) + j := by omega
    have h2 : m = (m - i) + i := by omega
    rw [h1, Function.iterate_add_apply, ← hfij, ← Function.iterate_add_apply, ← h2]
  have hmul : ∀ c, ∀ m, i ≤ m → ∀ d, f^[m + c * p] d = f^[m] d := by
    intro c
    induction c with
    | zero => intro m _ d; simp
    | succ c ih =>
        intro m hm d
        have : m + (c + 1) * p = (m + c * p) + p := by ring
        rw [this, hstep (m + c * p) (by omega) d, ih m hm d]
  refine ⟨p * (i + 1), by positivity, fun d => ?_⟩
  have hge : i ≤ p * (i + 1) := by nlinarith
  have := hmul (i + 1) (p * (i + 1)) hge d
  rw [← Function.iterate_add_apply]
  calc f^[p * (i + 1) + p * (i + 1)] d
      = f^[p * (i + 1) + (i + 1) * p] d := by ring_nf
    _ = f^[p * (i + 1)] d := this
