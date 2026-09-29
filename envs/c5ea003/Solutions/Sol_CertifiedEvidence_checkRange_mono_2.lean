-- Prove2me | solution 2 for CertifiedEvidence.checkRange_mono
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T09:09:17.116389+00:00
-- url     : https://prove2.me/submissions/faef017a-e2ae-4290-9e46-d3ffa7ee5ead

/-
# `CertifiedEvidence.checkRange_mono`
Target `a68844bb` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle screened CLEAN. Gift: **SAFE** per scripts/gift_check.py, which now agrees
with ship_one's live guard on four cases including one out-of-sample prediction. Guard is authority.

WHY THIS ONE, AND IN THIS ORDER. The real gift map of this bundle is a CHAIN:
    keystone 71917cc5  ->  gifts c219f37a, f3a9a5e4
    c219f37a           ->  gifts 39311ae8, ddf673ab
    f3a9a5e4           ->  gifts 1e06e373
    LEAVES (safe now)  :  a68844bb (this), 1e06e373, 39311ae8, ddf673ab
So the bundle must be worked BOTTOM-UP. Three ships were stopped by the guard before I saw this.

STATEMENT, verbatim:
    {p : ℕ → Bool} {lo hi lo' hi' : ℕ} (h : checkRange p lo hi = true)
      (h1 : lo ≤ lo') (h2 : hi' ≤ hi) : checkRange p lo' hi' = true

MATHS. Shrinking the window preserves a passing check. Both sides unfold definitionally
(`checkRange p a b` IS `checkFrom p a (b + 1 - a)`), so the keystone converts `h` into a bounded
quantifier over `[lo, hi]` and rebuilds one over `[lo', hi']`. The only obligations are that each
`j` in the smaller window lies in the larger one — linear, and `omega` covers the degenerate cases
where either window is EMPTY (truncated ℕ-subtraction makes the length 0, so the bound reads `j < a`,
contradicting `a ≤ j`, and the branch is vacuous rather than arithmetically true).

The keystone is RE-DERIVED INLINE; importing it from `Theorems/` would force the reduction path.
The inner binder is named `m`, not `lo`, so it cannot shadow the theorem's own `lo`.
-/
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core

set_option autoImplicit false
set_option maxHeartbeats 400000

open CertifiedEvidence

open CertifiedEvidence in
/-- **The target, verbatim.** -/
theorem solution {p : ℕ → Bool} {lo hi lo' hi' : ℕ} (h : checkRange p lo hi = true)
    (h1 : lo ≤ lo') (h2 : hi' ≤ hi) : checkRange p lo' hi' = true := by
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
  have h' : checkFrom p lo (hi + 1 - lo) = true := h
  have hall := (key (hi + 1 - lo) lo).mp h'
  show checkFrom p lo' (hi' + 1 - lo') = true
  exact (key (hi' + 1 - lo') lo').mpr (fun j hj1 hj2 => hall j (by omega) (by omega))
