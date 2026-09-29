-- Prove2me | solution 2 for CertifiedEvidence.exists_counterexample_of_checkRange_false
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T09:09:25.384063+00:00
-- url     : https://prove2.me/submissions/44317333-6e23-45f3-bcdd-8ea20fdcd093

/-
# `CertifiedEvidence.exists_counterexample_of_checkRange_false`
Target `1e06e373` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle screened CLEAN. Gift: **SAFE** (a leaf of this bundle's gift chain, per
scripts/gift_check.py, which now agrees with ship_one's live guard on four cases including one
out-of-sample prediction). The live guard remains the authority at ship time.

MATHS — the contrapositive of `checkRange_of`. Suppose no counterexample exists in `[lo, hi]`. Then
`p` is `true` throughout the window, so the keystone's `mpr` rebuilds `checkRange p lo hi = true`,
contradicting the hypothesis that it is `false`.

TWO POINTS OF CARE:
  * `push_neg` turns `¬ ∃ k, lo ≤ k ∧ k ≤ hi ∧ p k = false` into `∀ k, lo ≤ k → k ≤ hi → p k ≠ false`.
    Going from `p j ≠ false` to `p j = true` is NOT `rfl` — it is case analysis on a Bool. Done by
    `revert` + `cases p j <;> simp`, which handles both branches uniformly rather than relying on a
    lemma name I would be guessing at.
  * `checkRange p lo hi` is DEFINITIONALLY `checkFrom p lo (hi + 1 - lo)`, so the hypothesis retypes
    with no rewriting, and the window-bound obligation is linear (`omega`, which handles the empty
    window where truncated subtraction gives length 0).

The keystone is RE-DERIVED INLINE; importing it from `Theorems/` would force the reduction path.
-/
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core

set_option autoImplicit false
set_option maxHeartbeats 400000

open CertifiedEvidence

open CertifiedEvidence in
/-- **The target, verbatim.** -/
theorem solution {p : ℕ → Bool} {lo hi : ℕ} (h : checkRange p lo hi = false) :
    ∃ k, lo ≤ k ∧ k ≤ hi ∧ p k = false := by
  have key : ∀ (n m : ℕ), checkFrom p m n = true ↔ ∀ j, m ≤ j → j < m + n → p j = true := by
    intro n
    induction n with
    | zero =>
        intro m
        constructor
        · intro _ j hj1 hj2
          exfalso; omega
        · intro _
          rfl
    | succ n ih =>
        intro m
        simp only [checkFrom, Bool.and_eq_true, ih (m + 1)]
        constructor
        · rintro ⟨hm, hrest⟩ j hj1 hj2
          rcases Nat.eq_or_lt_of_le hj1 with hq | hq
          · subst hq; exact hm
          · exact hrest j (by omega) (by omega)
        · intro hall
          exact ⟨hall m le_rfl (by omega), fun j hj1 hj2 => hall j (by omega) (by omega)⟩
  by_contra hcon
  push_neg at hcon
  have hall : ∀ j, lo ≤ j → j < lo + (hi + 1 - lo) → p j = true := by
    intro j hj1 hj2
    have hne := hcon j hj1 (by omega)
    revert hne
    cases p j <;> simp
  have hTrue : checkFrom p lo (hi + 1 - lo) = true := (key (hi + 1 - lo) lo).mpr hall
  have hFalse : checkFrom p lo (hi + 1 - lo) = false := h
  rw [hFalse] at hTrue
  simp at hTrue
