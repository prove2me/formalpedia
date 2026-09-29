-- Prove2me | Theorems.Thm_CertifiedEvidence_exists_counterexample_of_checkRange_false
-- name    : CertifiedEvidence.exists_counterexample_of_checkRange_false
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:30:31.247517+00:00
-- url     : https://prove2.me/theorems/1e06e373-e15d-490a-a8ef-7b5eec676725
-- title:
--   A failing check produces an explicit counterexample.
-- statement:
--   A failing check produces an explicit counterexample.
--
--   ```lean
--   theorem CertifiedEvidence.exists_counterexample_of_checkRange_false{p : ℕ → Bool} {lo hi : ℕ}
--       (h : checkRange p lo hi = false) : ∃ k, lo ≤ k ∧ k ≤ hi ∧ p k = false := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CertifiedEvidence/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CertifiedEvidence/Core.lean#L188

-- Thm stub generated from MachineLearning/CertifiedEvidence/Core.lean
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

theorem CertifiedEvidence.exists_counterexample_of_checkRange_false{p : ℕ → Bool} {lo hi : ℕ}
    (h : checkRange p lo hi = false) : ∃ k, lo ≤ k ∧ k ≤ hi ∧ p k = false := by sorry
