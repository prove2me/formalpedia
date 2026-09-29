-- Prove2me | solution 2 for CertifiedEvidence.checkRange_of
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T09:17:06.399754+00:00
-- url     : https://prove2.me/submissions/ef29b7ee-4df8-4d39-9108-dd0fd0015d12

/-
# `CertifiedEvidence.checkRange_of`
Target `f3a9a5e4` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle screened CLEAN. Gift check: re-run with scripts/gift_check.py, which was
REBUILT after the old one was found to have a single reachable output ("SAFE") on every input.
The live guard in ship_one remains the authority.

ORDERING. This is one of the two conclusions that `checkFrom_eq_true_iff` (the keystone) would GIFT:
the live guard stopped that ship with `gifting: ['c219f37a','f3a9a5e4']`. Proving this conclusion
OUTRIGHT beats the sketch sitting on it, and once it and `of_checkRange` are Proved they can no longer
be gifted — which frees the keystone to be taken afterwards. Corollaries first, keystone last.

STATEMENT, verbatim from the platform:
    (p : ℕ → Bool) (lo hi : ℕ) (h : ∀ k, lo ≤ k → k ≤ hi → p k = true) : checkRange p lo hi = true

MATHS. `checkRange p lo hi` is DEFINITIONALLY `checkFrom p lo (hi + 1 - lo)`, so the goal retypes with
`show` and no rewriting. The keystone's `mpr` then needs
    `∀ j, lo ≤ j → j < lo + (hi + 1 - lo) → p j = true`
and `h` supplies `p j = true` from `lo ≤ j` and `j ≤ hi`. The gap is `j ≤ hi`, which is linear:
  * if `lo ≤ hi` the truncated subtraction is exact, `lo + (hi + 1 - lo) = hi + 1`, so `j < hi + 1`;
  * if `lo > hi` then `hi + 1 - lo = 0`, so `j < lo` contradicts `lo ≤ j` and the case is vacuous.
`omega` knows ℕ-subtraction and covers both without a manual split.

The keystone is RE-DERIVED INLINE: importing my own submission from `Theorems/` would force the
reduction path and an axiom audit, for twelve lines of structural induction.
-/
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core

set_option autoImplicit false
set_option maxHeartbeats 400000

open CertifiedEvidence

open CertifiedEvidence in
/-- **The target, verbatim.** -/
theorem solution (p : ℕ → Bool) (lo hi : ℕ) (h : ∀ k, lo ≤ k → k ≤ hi → p k = true) :
    checkRange p lo hi = true := by
  have key : ∀ (n lo : ℕ), checkFrom p lo n = true ↔ ∀ j, lo ≤ j → j < lo + n → p j = true := by
    intro n
    induction n with
    | zero =>
        intro lo
        constructor
        · intro _ j hj1 hj2
          exfalso; omega
        · intro _
          rfl
    | succ n ih =>
        intro lo
        simp only [checkFrom, Bool.and_eq_true, ih (lo + 1)]
        constructor
        · rintro ⟨hlo, hrest⟩ j hj1 hj2
          rcases Nat.eq_or_lt_of_le hj1 with hq | hq
          · subst hq; exact hlo
          · exact hrest j (by omega) (by omega)
        · intro hall
          exact ⟨hall lo le_rfl (by omega), fun j hj1 hj2 => hall j (by omega) (by omega)⟩
  show checkFrom p lo (hi + 1 - lo) = true
  exact (key (hi + 1 - lo) lo).mpr (fun j hj1 hj2 => h j hj1 (by omega))
