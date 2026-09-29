-- Prove2me | solution 1 for DestructiveVerification.verdict_batch
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:44:56.878274+00:00
-- url     : https://prove2.me/submissions/5013ed23-166a-4fb6-bf4e-612092052963

-- Sol generated from Combinatorics/DestructiveVerificationDepth.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
import Theorems.Thm_DestructiveVerification_residue_seq
import Theorems.Thm_DestructiveVerification_verdict_seq
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



lemma batch_succ (t : Test D) (n : ℕ) : batch t (n + 1) = seq (batch t n) t := rfl

/-- The residue of a batch is the iterated residue. -/
@[simp] lemma residue_batch (t : Test D) (n : ℕ) (d : D) :
    residue (batch t n) d = (residue t)^[n] d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
      rw [batch_succ, residue_seq, ih, Function.iterate_succ_apply']



/-! ## 6. Stabilisation: every test is nondestructive on its own core -/






open DestructiveVerification in
theorem solution(t : Test D) (n : ℕ) (d : D) :
    verdict (batch t n) d = true ↔ ∀ j < n, transcript t d j = true := by
  induction n with
  | zero => simp [batch, one, verdict]
  | succ n ih =>
      rw [batch_succ, verdict_seq, Bool.and_eq_true, ih, residue_batch]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h1 j hj
        · exact h2
      · intro h
        exact ⟨fun j hj => h j (by omega), h n (by omega)⟩
