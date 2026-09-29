-- Prove2me | solution 1 for Price2Adic.oddLeg_odd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T06:10:09.634621+00:00
-- url     : https://prove2.me/submissions/3bae2537-c9f0-4395-8ce8-b21c2f1fa923

/-
# `Price2Adic.oddLeg_odd`
Target `84a270b7` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.
(Chain screened: the bundle's `Definitions.` closure contains NO `Theorems.` import.)

    Valid (m, n)  =  0 < n ∧ n < m ∧ Nat.gcd m n = 1 ∧ (m + n) % 2 = 1
    oddLeg (m, n) =  m ^ 2 - n ^ 2          -- ℕ truncated subtraction

Claim: `oddLeg p % 2 = 1`.

`(m + n) % 2 = 1` forces m and n to have OPPOSITE parity; squaring preserves parity, so `m^2` and
`n^2` have opposite parity and their difference is odd. `n < m` gives `n^2 < m^2`, so the
subtraction is genuine and never clamps to 0.

VERIFIED EXHAUSTIVELY, not sampled: all 8076 Valid pairs with m < 200 — no counterexamples, no
clamping, and the tightest pairs `n = m-1` all give odd values.

WHICH HYPOTHESES ARE ACTUALLY USED — the check answered this too, and it shapes the proof:
  * `n < m`          USED — keeps the subtraction from truncating
  * `(m + n) % 2 = 1` USED — the parity engine
  * `0 < n`          unused
  * `Nat.gcd m n = 1` **UNUSED** — re-verified by dropping it entirely: still no counterexamples
So the proof destructures `Valid` but only binds the second and fourth components.
-/
import Mathlib
import Definitions.Def_Cryptography_Price2Adic_Tree

set_option autoImplicit false
set_option maxHeartbeats 400000

open Price2Adic in
/-- **The target, verbatim.** -/
theorem solution (p : ℕ × ℕ) (hp : Valid p) : oddLeg p % 2 = 1 := by
  obtain ⟨m, n⟩ := p
  obtain ⟨-, hlt, -, hpar⟩ := hp
  show (m ^ 2 - n ^ 2) % 2 = 1
  -- n < m gives n^2 < m^2, so the truncated subtraction is genuine
  have hle : n ^ 2 ≤ m ^ 2 := le_of_lt (Nat.pow_lt_pow_left hlt (by norm_num))
  -- `Nat.odd_sub` speaks about the truncated subtraction DIRECTLY, so no squares
  -- ever reach `omega`: it reduces oddness of the difference to parities of the squares,
  -- and `Nat.even_pow` reduces those to parities of m and n.
  rw [← Nat.odd_iff, Nat.odd_sub hle, Nat.even_pow, ← Nat.not_even_iff_odd, Nat.even_pow]
  -- remaining goal is a propositional statement about `Even m` and `Even n`;
  -- the parity hypothesis (m + n) odd says they differ.
  have hmn : ¬ (Even m ↔ Even n) := by
    rw [← Nat.even_add]
    simpa [Nat.even_iff] using hpar
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
  tauto
