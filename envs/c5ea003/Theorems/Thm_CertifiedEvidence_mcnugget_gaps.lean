-- Prove2me | Theorems.Thm_CertifiedEvidence_mcnugget_gaps
-- name    : CertifiedEvidence.mcnugget_gaps
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:30:47.957195+00:00
-- url     : https://prove2.me/theorems/4801d159-8ec1-493a-9c3d-4c3380579ce5
-- title:
--   The complete picture for `⟨3,5⟩`: the set of gaps is exactly `{1,2,4,7}`,
-- statement:
--   The complete picture for `⟨3,5⟩`: the set of gaps is exactly `{1,2,4,7}`,
--   so certification above the Frobenius number is not merely sufficient but sharp.
--
--   ```lean
--   theorem CertifiedEvidence.mcnugget_gaps(n : ℕ) :
--       (∃ x y : ℕ, n = 3 * x + 5 * y) ↔ n ∉ ({1, 2, 4, 7} : Finset ℕ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CertifiedEvidence/Sufficiency.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CertifiedEvidence/Sufficiency.lean#L175

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



/-! ## §3. Certified universal theorem I: a period-10 certificate -/




/-! ## §4. Certified universal theorem II: the numerical semigroup `⟨3,5⟩` -/

theorem CertifiedEvidence.mcnugget_gaps(n : ℕ) :
    (∃ x y : ℕ, n = 3 * x + 5 * y) ↔ n ∉ ({1, 2, 4, 7} : Finset ℕ) := by sorry
