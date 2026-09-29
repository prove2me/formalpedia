-- Prove2me | solution 1 for CertifiedEvidence.mcnugget_gaps
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:42:56.430184+00:00
-- url     : https://prove2.me/submissions/d92ec52e-6da5-4262-96a3-aa0efef61759

-- Sol generated from MachineLearning/CertifiedEvidence/Sufficiency.lean
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core
import Definitions.Def_MachineLearning_CertifiedEvidence_Sufficiency
import Theorems.Thm_CertifiedEvidence_shift_certifies
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


theorem repr35_iff (n : ℕ) : repr35 n = true ↔ ∃ x y : ℕ, n = 3 * x + 5 * y := by
  rw [repr35, List.any_eq_true]
  constructor
  · rintro ⟨y, -, hy⟩
    rw [decide_eq_true_iff] at hy
    exact ⟨(n - 5 * y) / 3, y, by omega⟩
  · rintro ⟨x, y, h⟩
    refine ⟨y, List.mem_range.mpr (by omega), ?_⟩
    rw [decide_eq_true_iff]
    omega

theorem repr35_closed (n : ℕ) (h : repr35 n = true) : repr35 (n + 3) = true := by
  obtain ⟨x, y, hxy⟩ := (repr35_iff n).mp h
  exact (repr35_iff (n + 3)).mpr ⟨x + 1, y, by omega⟩

/-- **Chicken McNugget, certified.** Three kernel-checked inputs (`8, 9, 10`)
plus closure under `+3` prove that every `n ≥ 8` is a non-negative integer
combination of `3` and `5`. -/
theorem mcnugget_ge_eight (n : ℕ) (hn : 8 ≤ n) : ∃ x y : ℕ, n = 3 * x + 5 * y :=
  (repr35_iff n).mp (shift_certifies (N := 8) (a := 3) (by norm_num) (by decide)
    (fun m _ hm => repr35_closed m hm) n hn)




open CertifiedEvidence in
theorem solution(n : ℕ) :
    (∃ x y : ℕ, n = 3 * x + 5 * y) ↔ n ∉ ({1, 2, 4, 7} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, y, rfl⟩ hmem
    rcases hmem with h | h | h | h <;> omega
  · intro hmem
    push_neg at hmem
    rcases Nat.lt_or_ge n 8 with hlt | hge
    · have hn : n = 0 ∨ n = 3 ∨ n = 5 ∨ n = 6 := by omega
      rcases hn with rfl | rfl | rfl | rfl
      exacts [⟨0, 0, rfl⟩, ⟨1, 0, rfl⟩, ⟨0, 1, rfl⟩, ⟨2, 0, rfl⟩]
    · exact mcnugget_ge_eight n hge
