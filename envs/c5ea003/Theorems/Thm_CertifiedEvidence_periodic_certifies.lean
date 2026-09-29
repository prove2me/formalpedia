-- Prove2me | Theorems.Thm_CertifiedEvidence_periodic_certifies
-- name    : CertifiedEvidence.periodic_certifies
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:30:51.666218+00:00
-- url     : https://prove2.me/theorems/39311ae8-ed78-40ac-98e0-0b832cecb3a5
-- title:
--   Periodic certificate.
-- statement:
--   **Periodic certificate.** If `p` has period `T > 0`, checking one full period
--   proves the universal statement.
--
--   ```lean
--   theorem CertifiedEvidence.periodic_certifies{p : ℕ → Bool} {T : ℕ} (hT : 0 < T)
--       (hper : ∀ n, p (n + T) = p n) (hbase : checkRange p 1 T = true) :
--       ∀ n, 1 ≤ n → p n = true := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CertifiedEvidence/Sufficiency.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CertifiedEvidence/Sufficiency.lean#L85

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




/-! ## §2. Structural hypotheses that yield descent -/

theorem CertifiedEvidence.periodic_certifies{p : ℕ → Bool} {T : ℕ} (hT : 0 < T)
    (hper : ∀ n, p (n + T) = p n) (hbase : checkRange p 1 T = true) :
    ∀ n, 1 ≤ n → p n = true := by sorry
