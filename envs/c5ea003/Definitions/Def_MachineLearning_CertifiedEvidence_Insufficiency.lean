-- Prove2me | Definitions.Def_MachineLearning_CertifiedEvidence_Insufficiency
-- name    : MachineLearning_CertifiedEvidence_Insufficiency
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:38:45.518359+00:00
-- url     : https://prove2.me/theorems/8f3989c9-e751-4573-9a68-47835169c3ba
-- title:
--   Aether Catalog definitions — MachineLearning_CertifiedEvidence_Insufficiency
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.CertifiedEvidence.Insufficiency`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/CertifiedEvidence/Insufficiency.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The exact logical strength of a finite certificate

`CertifiedEvidence.Core` gives a checker whose success on `[1, N]` is *equivalent*
to the bounded statement `∀ k ∈ [1,N], p k`.  This file measures how far that is
from the universal statement `∀ k ≥ 1, p k`, and the answer is: infinitely far,
uniformly in `N`, for a reason that is exactly the learning-theoretic one.

## Main results

* `truncate_agrees` / `truncate_fails` — the truncation operator produces, from
  any checker, a checker with the *same* evidence on `[1,N]` and an explicit
  counterexample at `N+1`.
* `finite_check_not_sound` — for every bound `N` there is a predicate passing
  the `N`-certificate and failing universally: no finite bound is a proof.
* `no_uniform_bound` — the diagonal form: there is no bound `N` that works for
  all predicates simultaneously.
* `versionSpace_infinite`, `continuum_le_versionSpace` — the *version space*
  (the set of hypotheses consistent with the evidence) after any finite amount
  of evidence still has the cardinality of the continuum.  Finite evidence
  removes no positive fraction of the hypothesis space.
* `no_finite_sample_determines` — no finite sample pins down a hypothesis: the
  class `ℕ → Bool` shatters every finite set, i.e. it has infinite VC dimension.
  This is the learning-theoretic reading of the previous item.
* `evidence_monotone_but_never_sufficient` — the two facts combined: evidence
  is monotone in `N` (more computation never hurts) yet its limit is not the
  universal statement for any single `N`.
-/


namespace CertifiedEvidence

/-! ## §1. Truncation: evidence-preserving sabotage -/

/-- `truncate p N` agrees with `p` on `[0, N]` and is `false` afterwards. -/
def truncate (p : ℕ → Bool) (N : ℕ) : ℕ → Bool := fun k => p k && decide (k ≤ N)





/-! ## §2. No finite bound is a proof -/




/-! ## §3. The version space after finite evidence -/

/-- The set of hypotheses consistent with the evidence collected on `[1,N]`. -/
def versionSpace (p : ℕ → Bool) (N : ℕ) : Set (ℕ → Bool) :=
  {q | ∀ k, 1 ≤ k → k ≤ N → q k = p k}

/-- The canonical way to build a consistent hypothesis out of arbitrary behaviour
beyond the evidence window. -/
def extendBeyond (p : ℕ → Bool) (N : ℕ) (f : ℕ → Bool) : ℕ → Bool :=
  fun k => if k ≤ N then p k else f (k - (N + 1))





/-! ## §4. The learning-theoretic reading: infinite VC dimension -/



end CertifiedEvidence


