-- Prove2me | solution 2 for CertifiedEvidence.periodic_certifies
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T09:09:38.026146+00:00
-- url     : https://prove2.me/submissions/c129bcbc-a27c-4899-96e2-d5f494df1329

/-
# `CertifiedEvidence.periodic_certifies`
Target `39311ae8` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle screened CLEAN. Gift: **SAFE** (leaf of this bundle's gift chain).

MATHS. A periodic predicate verified on ONE period holds forever. Given period `T > 0`, periodicity
`p (n + T) = p n`, and a base check over `[1, T]`, descend by `T` until landing in the base window.

  * `n ≤ T` — then `1 ≤ n ≤ T`, so the base check gives `p n = true` directly.
  * `n > T` — put `m = n - T`. Then `1 ≤ m` (as `n > T ≥ 1`) and `m < n` (as `T > 0`), so the strong
    induction hypothesis applies; and `m + T = n` because `T ≤ n`, so `hper m : p (m + T) = p m`
    transports the result up.

PROBED, NOT GUESSED — pinned from real Mathlib call sites rather than from a remembered name:
  * `Nat.strong_induction_on {p : ℕ → Prop} (n : ℕ)` — Data/Nat/Init.lean:294. This is the right tool
    because the descent is by `T`, an arbitrary positive amount; `Nat.le_induction` steps by ONE and
    cannot express it.
  * The CASE NAME varies across call sites (`| ind n ih`, `| h n ih`, `| _ i h`), so `| _ n ih` is
    used here — the form two call sites confirm works generically.
  * `intro n` FIRST, leaving `1 ≤ n → p n = true` as the motive, so `ih : ∀ m, m < n → 1 ≤ m → …`.

The keystone `checkFrom_eq_true_iff` is RE-DERIVED INLINE; importing it from `Theorems/` would force
the reduction path and an axiom audit.
-/
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core

set_option autoImplicit false
set_option maxHeartbeats 400000

open CertifiedEvidence

open CertifiedEvidence in
/-- **The target, verbatim.** -/
theorem solution {p : ℕ → Bool} {T : ℕ} (hT : 0 < T)
    (hper : ∀ n, p (n + T) = p n) (hbase : checkRange p 1 T = true) :
    ∀ n, 1 ≤ n → p n = true := by
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
  -- the base window, as a bounded quantifier over [1, T]
  have hb : ∀ j, 1 ≤ j → j < 1 + (T + 1 - 1) → p j = true :=
    (key (T + 1 - 1) 1).mp hbase
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro hn
      by_cases hle : n ≤ T
      · exact hb n hn (by omega)
      · have hlt : n - T < n := by omega
        have h1 : 1 ≤ n - T := by omega
        have hrec : p (n - T) = true := ih (n - T) hlt h1
        have hsum : n - T + T = n := by omega
        have := hper (n - T)
        rw [hsum] at this
        rw [this]
        exact hrec
