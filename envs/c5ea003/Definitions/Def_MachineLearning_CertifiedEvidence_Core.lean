-- Prove2me | Definitions.Def_MachineLearning_CertifiedEvidence_Core
-- name    : MachineLearning_CertifiedEvidence_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:38:14.864516+00:00
-- url     : https://prove2.me/theorems/306231cb-c508-4d65-89cb-723a209ae9d7
-- title:
--   Aether Catalog definitions — MachineLearning_CertifiedEvidence_Core
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.CertifiedEvidence.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/CertifiedEvidence/Core.lean by skeleton subtraction
import Mathlib
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


namespace CertifiedEvidence

/-! ## §1. The bounded conjunction -/

/-- `checkFrom p lo n` is `true` iff `p` holds at each of `lo, lo+1, …, lo+n-1`.
Structural recursion on the *length* `n` keeps kernel reduction linear. -/
def checkFrom (p : ℕ → Bool) (lo : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => p lo && checkFrom p (lo + 1) n

/-- `checkRange p lo hi` is `true` iff `p` holds on the closed window
`[lo, hi]`. For `hi < lo` the window is empty and the check succeeds. -/
def checkRange (p : ℕ → Bool) (lo hi : ℕ) : Bool := checkFrom p lo (hi + 1 - lo)



/-! ## §2. Soundness and completeness of the checker -/





/-! ## §3. The composition law: chunked and resumable certification -/





/-! ## §4. Alternative implementations: list and array traversal -/



/-! ## §5. Certificate extraction: explicit counterexamples -/

/-- The first failure of `p` in the window of length `n` starting at `lo`. -/
def firstFail (p : ℕ → Bool) (lo : ℕ) : ℕ → Option ℕ
  | 0 => none
  | n + 1 => if p lo then firstFail p (lo + 1) n else some lo




end CertifiedEvidence


