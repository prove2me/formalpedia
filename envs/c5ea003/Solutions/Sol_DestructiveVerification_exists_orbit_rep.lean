-- Prove2me | solution 1 for DestructiveVerification.exists_orbit_rep
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:43:14.180657+00:00
-- url     : https://prove2.me/submissions/f6176a06-49e2-450e-8576-e1049729642a

-- Sol generated from Combinatorics/DestructiveVerificationDepth.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
import Theorems.Thm_DestructiveVerification_exists_orbit_recurrence
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
theorem solution[Fintype D] (f : D → D) (d : D) (m : ℕ) :
    ∃ j < Fintype.card D, f^[m] d = f^[j] d := by
  obtain ⟨i, p, hp, hip, hper⟩ := exists_orbit_recurrence f d
  by_cases hm : m < i
  · exact ⟨m, by omega, rfl⟩
  · push_neg at hm
    have hy : Function.IsPeriodicPt f p (f^[i] d) := by
      show f^[p] (f^[i] d) = f^[i] d
      rw [← Function.iterate_add_apply, Nat.add_comm p i]
      exact hper
    refine ⟨i + (m - i) % p, by have := Nat.mod_lt (m - i) hp; omega, ?_⟩
    have h1 : f^[m] d = f^[m - i] (f^[i] d) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    have h2 : f^[i + (m - i) % p] d = f^[(m - i) % p] (f^[i] d) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [h1, h2, hy.iterate_mod_apply]
