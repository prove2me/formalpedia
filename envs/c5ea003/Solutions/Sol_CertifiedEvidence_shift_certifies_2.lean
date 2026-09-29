-- Prove2me | solution 2 for CertifiedEvidence.shift_certifies
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T09:13:22.899855+00:00
-- url     : https://prove2.me/submissions/475657c2-d17a-478e-a51b-b1251833a4a8

/-
# `CertifiedEvidence.shift_certifies`
Target `ddf673ab` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle screened CLEAN. Gift: **SAFE** (leaf of this bundle's gift chain).

MATHS. An induction principle with an arbitrary stride `a`: check the first `a` values explicitly,
then propagate by the closure rule `p n → p (n + a)`.

  * `n < N + a` — the base window `[N, N + a - 1]` already covers `n`, so the check gives `p n`.
  * `n ≥ N + a` — put `m = n - a`. Then `N ≤ m` (as `n ≥ N + a`) and `m < n` (as `a > 0`), so the
    strong induction hypothesis gives `p m = true`; `hclosed m` lifts it to `p (m + a)`, and
    `m + a = n` because `a ≤ n`.

The two branches are exactly the two ways `n` can sit relative to the base window, and the split is
`by_cases` on `n < N + a`.

PROBED, NOT GUESSED — same pinning as the periodic sibling:
  * `Nat.strong_induction_on {p : ℕ → Prop} (n : ℕ)` (Data/Nat/Init.lean:294); the descent is by `a`,
    an arbitrary positive stride, which `Nat.le_induction` (step of one) cannot express.
  * case name written `| _ n ih` because it VARIES across Mathlib call sites (`ind`, `h`, `_`).
  * `intro n` first, so the motive is `N ≤ n → p n = true` and `ih : ∀ m, m < n → N ≤ m → …`.

NOTE ON THE BASE WINDOW. `checkRange p N (N + a - 1)` has length `(N + a - 1) + 1 - N`, which is `a`
exactly when `a > 0` — the hypothesis `ha` is load-bearing here, not decoration, and `omega` needs it
to see that the truncated subtraction does not collapse.

The keystone is RE-DERIVED INLINE; importing it from `Theorems/` would force the reduction path.
-/
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core

set_option autoImplicit false
set_option maxHeartbeats 400000

open CertifiedEvidence

open CertifiedEvidence in
/-- **The target, verbatim.** -/
theorem solution {p : ℕ → Bool} {N a : ℕ} (ha : 0 < a)
    (hbase : checkRange p N (N + a - 1) = true)
    (hclosed : ∀ n, N ≤ n → p n = true → p (n + a) = true) :
    ∀ n, N ≤ n → p n = true := by
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
  have hb : ∀ j, N ≤ j → j < N + ((N + a - 1) + 1 - N) → p j = true :=
    (key ((N + a - 1) + 1 - N) N).mp hbase
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro hn
      by_cases hlt : n < N + a
      · exact hb n hn (by omega)
      · have hlt' : n - a < n := by omega
        have hN : N ≤ n - a := by omega
        have hrec : p (n - a) = true := ih (n - a) hlt' hN
        have hsum : n - a + a = n := by omega
        have := hclosed (n - a) hN hrec
        rw [hsum] at this
        exact this
