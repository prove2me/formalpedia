-- Prove2me | solution 1 for CertifiedEvidence.firstFail_spec
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:41:23.511799+00:00
-- url     : https://prove2.me/submissions/640d775b-95a9-4b07-8f75-1323795b03d9

-- Sol generated from MachineLearning/CertifiedEvidence/Core.lean
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core
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





/-! ## §3. The composition law: chunked and resumable certification -/





/-! ## §4. Alternative implementations: list and array traversal -/



/-! ## §5. Certificate extraction: explicit counterexamples -/






open CertifiedEvidence in
theorem solution(p : ℕ → Bool) :
    ∀ (n lo k : ℕ), firstFail p lo n = some k → lo ≤ k ∧ k < lo + n ∧ p k = false := by
  intro n
  induction n with
  | zero => intro lo k h; simp [firstFail] at h
  | succ n ih =>
      intro lo k h
      by_cases hp : p lo = true
      · rw [firstFail, if_pos hp] at h
        obtain ⟨h1, h2, h3⟩ := ih (lo + 1) k h
        exact ⟨by omega, by omega, h3⟩
      · rw [firstFail, if_neg hp] at h
        have hk : k = lo := by simpa using h.symm
        subst hk
        exact ⟨le_rfl, by omega, by simpa using hp⟩
