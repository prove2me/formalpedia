-- Prove2me | Definitions.Def_MachineLearning_CertifiedEvidence_Sufficiency
-- name    : MachineLearning_CertifiedEvidence_Sufficiency
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:38:44.692841+00:00
-- url     : https://prove2.me/theorems/a9666172-b7e6-44d0-8cb6-169680cce499
-- title:
--   Aether Catalog definitions — MachineLearning_CertifiedEvidence_Sufficiency
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.CertifiedEvidence.Sufficiency`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/CertifiedEvidence/Sufficiency.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# When finite computation *does* prove a universal statement

`CertifiedEvidence.Insufficiency` shows that a finite certificate alone never
entails a universal claim.  The remedy is not more computation but *structure*:
a finite window plus a proof that every larger input reduces to a smaller one.
This file isolates that pattern as a first-class object, proves it is both sound
and — the point of the file — **complete**:

* `DescentCertificate` — a finite verified window `[1,N]` together with a
  reduction `r` that strictly decreases above `N` and transports truth upwards.
* `DescentCertificate.sound` — strong induction turns such a certificate into
  the universal statement.
* `descentCertificate_nonempty_iff` — *every* true universal statement of this
  form admits a descent certificate.  So "finite check + descent" is a complete
  proof system for `∀ n ≥ 1, p n`, in exact contrast with the incompleteness of
  "finite check" alone.
* `periodic_certifies`, `shift_certifies` — the two structural hypotheses that
  occur in practice (periodicity, closure under adding a fixed step) are
  instances of descent.
* Two fully certified universal theorems obtained from tiny kernel checks:
  `pow_five_mod_ten` (period-10 certificate, 10 checked inputs) and
  `mcnugget_ge_eight` with `mcnugget_seven` (a 3-input window plus `+3`-closure
  gives the numerical-semigroup statement and its sharp Frobenius boundary).
-/


namespace CertifiedEvidence

/-! ## §1. Descent certificates -/

/-- A **descent certificate** for `p`: a kernel-checked initial window `[1,N]`
together with a reduction `reduce` which, above `N`, produces a strictly smaller
positive input whose success implies success at the original input. -/
structure DescentCertificate (p : ℕ → Bool) where
  /-- The size of the finite window that is checked by computation. -/
  bound : ℕ
  /-- The reduction used above the window. -/
  reduce : ℕ → ℕ
  /-- The kernel-checked evidence. -/
  base : checkRange p 1 bound = true
  /-- The reduction stays in the domain of the statement. -/
  reduce_pos : ∀ n, bound < n → 1 ≤ reduce n
  /-- The reduction strictly decreases, so the induction is well founded. -/
  reduce_lt : ∀ n, bound < n → reduce n < n
  /-- Truth is transported from the reduced input back to the original one. -/
  step : ∀ n, bound < n → p (reduce n) = true → p n = true



/-! ## §2. Structural hypotheses that yield descent -/



/-! ## §3. Certified universal theorem I: a period-10 certificate -/

/-- The checker for the last digit of a fifth power. -/
def lastDigitPow5 (n : ℕ) : Bool := decide (n ^ 5 % 10 = n % 10)



/-! ## §4. Certified universal theorem II: the numerical semigroup `⟨3,5⟩` -/

/-- The checker for representability as `3x + 5y`: a bounded search over the
possible values of `y`, evaluable by the kernel. -/
def repr35 (n : ℕ) : Bool :=
  (List.range (n + 1)).any (fun y => decide (5 * y ≤ n ∧ (n - 5 * y) % 3 = 0))






end CertifiedEvidence


