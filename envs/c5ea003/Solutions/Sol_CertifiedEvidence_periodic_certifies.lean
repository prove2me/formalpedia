-- Prove2me | solution 1 for CertifiedEvidence.periodic_certifies
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:42:57.5389+00:00
-- url     : https://prove2.me/submissions/c187a34e-6442-4a24-a91c-19fa9b0e8f0c

-- Sol generated from MachineLearning/CertifiedEvidence/Sufficiency.lean
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core
import Definitions.Def_MachineLearning_CertifiedEvidence_Sufficiency
import Theorems.Thm_CertifiedEvidence_of_checkRange
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


/-- **Soundness.** A descent certificate proves the universal statement. -/
theorem DescentCertificate.sound {p : ℕ → Bool} (c : DescentCertificate p) :
    ∀ n, 1 ≤ n → p n = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro hn
      by_cases h : n ≤ c.bound
      · exact of_checkRange c.base hn h
      · push_neg at h
        exact c.step n h (ih (c.reduce n) (c.reduce_lt n h) (c.reduce_pos n h))


/-! ## §2. Structural hypotheses that yield descent -/



/-! ## §3. Certified universal theorem I: a period-10 certificate -/




/-! ## §4. Certified universal theorem II: the numerical semigroup `⟨3,5⟩` -/








open CertifiedEvidence in
theorem solution{p : ℕ → Bool} {T : ℕ} (hT : 0 < T)
    (hper : ∀ n, p (n + T) = p n) (hbase : checkRange p 1 T = true) :
    ∀ n, 1 ≤ n → p n = true := by
  refine DescentCertificate.sound
    { bound := T, reduce := fun n => n - T, base := hbase
      reduce_pos := fun n hn => by omega
      reduce_lt := fun n hn => by omega
      step := fun n hn h => ?_ }
  have hn' : n - T + T = n := by omega
  rw [← hn', hper]
  exact h
