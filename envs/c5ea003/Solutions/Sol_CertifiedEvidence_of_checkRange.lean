-- Prove2me | solution 1 for CertifiedEvidence.of_checkRange
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:39:33.12973+00:00
-- url     : https://prove2.me/submissions/33d47ac0-2bae-45d7-8862-5dd2ac123fce

-- Sol generated from MachineLearning/CertifiedEvidence/Core.lean
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core
import Theorems.Thm_CertifiedEvidence_checkFrom_eq_true_iff
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A verified reflection kernel for bounded universal statements

Certified computation in a proof assistant proceeds in two steps: a *checker*
`c : ℕ → Bool` is evaluated by the kernel on a finite window, and a *soundness
theorem* converts the resulting `true` into a mathematical statement.  This file
builds the reflection layer once and for all, with every law an efficient
implementation needs:

* `checkFrom` / `checkRange` — the bounded conjunction `⋀_{lo ≤ k ≤ hi} p k`,
  written as a structurally recursive `Bool` program the kernel can evaluate.
* `checkRange_eq_true_iff` — the soundness *and* completeness bridge.
* `checkFrom_add`, `checkRange_glue` — the composition law that makes
  divide-and-conquer (chunked, parallel, or resumable) certification correct:
  a certificate for `[lo, hi]` is exactly a pair of certificates for
  `[lo, mid]` and `[mid+1, hi]`.
* `checkFrom_eq_listAll`, `checkFrom_eq_arrayAll` — the same predicate computed
  by `List.range'`/`Array` traversal, so a fast array implementation can be
  substituted for the naive recursion without enlarging the trusted base.
* `firstFail` — certificate *extraction*: a failing check returns an explicit
  counterexample together with a proof that it is one.

Nothing here is specific to a particular conjecture; the files
`CertifiedEvidence.Insufficiency`, `CertifiedEvidence.Sufficiency` and
`CertifiedEvidence.Collatz` use this kernel to delimit exactly what finite
computation can and cannot prove.
-/


open CertifiedEvidence

/-! ## §1. The bounded conjunction -/





/-! ## §2. Soundness and completeness of the checker -/


/-- The reflection bridge for a closed window. -/
theorem checkRange_eq_true_iff (p : ℕ → Bool) (lo hi : ℕ) :
    checkRange p lo hi = true ↔ ∀ k, lo ≤ k → k ≤ hi → p k = true := by
  rw [checkRange, checkFrom_eq_true_iff]
  constructor
  · intro h k hk hk'
    exact h k hk (by omega)
  · intro h k hk hk'
    exact h k hk (by omega)



/-! ## §3. The composition law: chunked and resumable certification -/





/-! ## §4. Alternative implementations: list and array traversal -/



/-! ## §5. Certificate extraction: explicit counterexamples -/






open CertifiedEvidence in
theorem solution{p : ℕ → Bool} {lo hi : ℕ} (h : checkRange p lo hi = true)
    {k : ℕ} (h1 : lo ≤ k) (h2 : k ≤ hi) : p k = true :=
  (checkRange_eq_true_iff p lo hi).mp h k h1 h2
