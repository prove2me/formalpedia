-- Prove2me | solution 1 for DestructiveVerification.residue_bijOn_core
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:48:54.838136+00:00
-- url     : https://prove2.me/submissions/f02a89c5-93bc-4e0b-9843-f3594744546b

-- Sol generated from Combinatorics/DestructiveVerificationDepth.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
import Theorems.Thm_DestructiveVerification_exists_idempotent_iterate
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
theorem solution[Finite D] (t : Test D) :
    ∃ N, 0 < N ∧ Set.BijOn (residue t) (Set.range ((residue t)^[N]))
      (Set.range ((residue t)^[N])) := by
  set f := residue t with hf
  obtain ⟨N, hN, hid⟩ := exists_idempotent_iterate f
  refine ⟨N, hN, ?_⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hfix : ∀ x ∈ Set.range (f^[M + 1]), f^[M + 1] x = x := by
    rintro x ⟨a, rfl⟩; exact hid a
  have hcomm : ∀ (m : ℕ) (x : D), f^[m] (f x) = f (f^[m] x) := by
    intro m x
    rw [← Function.iterate_succ_apply f m x, Function.iterate_succ_apply']
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨a, rfl⟩
    exact ⟨f a, hcomm _ a⟩
  · intro x hx y hy hxy
    have hx2 : f^[M] (f x) = x := by
      rw [← Function.iterate_succ_apply]; exact hfix x hx
    have hy2 : f^[M] (f y) = y := by
      rw [← Function.iterate_succ_apply]; exact hfix y hy
    rw [← hx2, hxy, hy2]
  · rintro x hx
    have hx' : f^[M + 1] x = x := hfix x hx
    refine ⟨f^[M] x, ⟨f^[M] x, ?_⟩, ?_⟩
    · rw [← Function.iterate_add_apply]
      have hMM : M + 1 + M = M + (M + 1) := by omega
      rw [hMM, Function.iterate_add_apply, hx']
    · exact (Function.iterate_succ_apply' f M x).symm.trans hx'
