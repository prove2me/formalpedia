-- Prove2me | solution 1 for CertifiedEvidence.checkFrom_eq_true_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T09:40:38.804314+00:00
-- url     : https://prove2.me/submissions/1c003e17-a5fd-40c6-9999-16c3f3de5716

/-
# `CertifiedEvidence.checkFrom_eq_true_iff`
Target `71917cc5` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle screened CLEAN (no `Theorems.` import). Gift check run separately.

THE KEYSTONE of this bundle: `of_checkRange`, `checkRange_mono`, `checkRange_of` and
`exists_counterexample_of_checkRange_false` all carry SKETCH_ACCEPTED and all reduce to this.
Taking it outright is the move that VOIDS those gifts rather than handing them over.

DEFINITION (read from the bundle, not guessed):

    def checkFrom (p : ℕ → Bool) (lo : ℕ) : ℕ → Bool
      | 0     => true
      | n + 1 => p lo && checkFrom p (lo + 1) n

so `checkFrom p lo n` asserts `p` holds on the n-element window `[lo, lo+n)`.

PROOF. Induction on `n`, generalising `lo` — note the statement quantifies `∀ n lo`, so `intro n`
leaves `∀ lo` inside the motive and the IH is available at `lo + 1`, which is exactly where the
recursion moves.

  * `n = 0`: the window is empty. Left side is `true` by the first equation. Right side is vacuous —
    `lo ≤ k` and `k < lo + 0` are contradictory — so `exfalso; omega`. (omega cannot prove the Bool
    goal `p k = true` directly; it discharges the contradictory hypotheses.)
  * `n+1`: unfold one step and split the conjunction with `Bool.and_eq_true`, then rewrite the tail
    with `ih (lo + 1)`. The obligation becomes
        `p lo = true ∧ (∀ k, lo+1 ≤ k → k < lo+1+n → p k) ↔ (∀ k, lo ≤ k → k < lo+(n+1) → p k)`
    Forward: given `lo ≤ k`, trichotomy on `lo = k` (use the head) or `lo < k` (use the tail).
    Backward: the head is the instance at `k = lo`; the tail is the hypothesis re-indexed.
    Every arithmetic side condition is linear, so `omega` closes each.
-/
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core

set_option autoImplicit false
set_option maxHeartbeats 400000

open CertifiedEvidence

open CertifiedEvidence in
/-- **The target, verbatim.** -/
theorem solution (p : ℕ → Bool) :
    ∀ (n lo : ℕ), checkFrom p lo n = true ↔ ∀ k, lo ≤ k → k < lo + n → p k = true := by
  intro n
  induction n with
  | zero =>
      intro lo
      constructor
      · intro _ k hk1 hk2
        exfalso; omega
      · intro _
        rfl
  | succ n ih =>
      intro lo
      simp only [checkFrom, Bool.and_eq_true, ih (lo + 1)]
      constructor
      · rintro ⟨hlo, hrest⟩ k hk1 hk2
        rcases Nat.eq_or_lt_of_le hk1 with h | h
        · subst h; exact hlo
        · exact hrest k (by omega) (by omega)
      · intro h
        exact ⟨h lo le_rfl (by omega), fun k hk1 hk2 => h k (by omega) (by omega)⟩
