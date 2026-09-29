-- Prove2me | Definitions.Def_Combinatorics_DestructiveVerificationDepth
-- name    : Combinatorics_DestructiveVerificationDepth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:32:38.797086+00:00
-- url     : https://prove2.me/theorems/7613ccb3-8c70-4bcd-9364-1f60da359a63
-- title:
--   Aether Catalog definitions — Combinatorics_DestructiveVerificationDepth
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.DestructiveVerificationDepth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/DestructiveVerificationDepth.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
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

namespace DestructiveVerification

variable {D : Type*}

/-! ## 1. Transcripts -/

/-- The **transcript** of a test on a dish: the verdict stream obtained by
re-running the test on each successive residue. -/
def transcript (t : Test D) (d : D) (k : ℕ) : Bool := verdict t ((residue t)^[k] d)






/-! ## 2. The orbit lemma -/



/-! ## 3. Rigidity: destruction depth is either infinite or `< #D` -/



/-! ## 4. Sharpness: a test of every destruction depth -/

/-- The **fuse test** on `k + 2` dishes: the dish is advanced one notch per run
and burns out at the last notch, where the verdict flips.  It accepts the
initial dish for exactly `k + 1` runs. -/
def fuseTest (k : ℕ) : Test (Fin (k + 2)) :=
  fun d => (decide (d.1 ≤ k), ⟨min (d.1 + 1) (k + 1), by omega⟩)





/-! ## 5. Batches: running a test `n` times in a row -/

/-- The **batch test** `batch t n`: run `t` exactly `n` times, each time on the
previous residue, and accept iff every run accepted. -/
def batch (t : Test D) : ℕ → Test D
  | 0 => one D
  | n + 1 => seq (batch t n) t






/-! ## 6. Stabilisation: every test is nondestructive on its own core -/





end DestructiveVerification


