-- Prove2me | Theorems.Thm_CertifiedEvidence_descentCertificate_nonempty_iff
-- name    : CertifiedEvidence.descentCertificate_nonempty_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:30:18.686699+00:00
-- url     : https://prove2.me/theorems/77813352-3346-4e89-a3ff-7eda59bddfa1
-- title:
--   Completeness.
-- statement:
--   **Completeness.** Conversely, every true universal statement has a descent
--   certificate — a trivial one, but its existence is what makes "finite check plus
--   descent" a complete proof system, unlike bare finite checking, which by
--   `finite_check_not_sound` is not even sound.
--
--   ```lean
--   theorem CertifiedEvidence.descentCertificate_nonempty_iff(p : ℕ → Bool) :
--       Nonempty (DescentCertificate p) ↔ ∀ n, 1 ≤ n → p n = true := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CertifiedEvidence/Sufficiency.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CertifiedEvidence/Sufficiency.lean#L65

-- Thm stub generated from MachineLearning/CertifiedEvidence/Sufficiency.lean
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core
import Definitions.Def_MachineLearning_CertifiedEvidence_Sufficiency
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


open CertifiedEvidence

/-! ## §1. Descent certificates -/

theorem CertifiedEvidence.descentCertificate_nonempty_iff(p : ℕ → Bool) :
    Nonempty (DescentCertificate p) ↔ ∀ n, 1 ≤ n → p n = true := by sorry
