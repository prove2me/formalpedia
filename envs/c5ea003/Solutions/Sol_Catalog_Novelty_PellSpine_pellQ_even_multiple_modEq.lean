-- Prove2me | solution 1 for Catalog.Novelty.PellSpine.pellQ_even_multiple_modEq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:04:56.763967+00:00
-- url     : https://prove2.me/submissions/9b21687c-b6a0-4ff7-a4b6-1d97114e5fc3

-- Sol generated from Novelty/PellSpineCompanionDivisibility.lean
import Mathlib
import Definitions.Def_Novelty_PellSpineCore
import Theorems.Thm_Catalog_Novelty_PellSpine_pellQ_add_two_mul_modEq
/-
# The companion divisibility law on the Pell spine

`Novelty.PellSpineDivisibility` shows that the Pell numbers `P` form a strong divisibility
sequence while the half-companion sequence `Q` does **not** (`gcd (Q 3) (Q 6) = 1`).  That
refutation leaves the real question open: *exactly when* does `Q m` divide `Q n`?

This file answers it completely.  For every `m ≥ 2`,

`Q m ∣ Q n  ↔  n = m * k for some odd k`,

a parity-graded divisibility law with no analogue among the `P`'s.  The proof runs in two
independent halves:

* **index step** — `Q m ∣ P (2m)` and `Q n ∣ P (2n)` push the hypothesis into the strong
  divisibility law for `P`, forcing `Q m ∣ P (2 gcd(m,n))`; if `gcd(m,n) < m` the divisor
  exceeds the dividend, so `m ∣ n`;
* **parity step** — modulo `Q m` the companion sequence satisfies the two-step recursion
  `Q (a + 2m) ≡ 2 P m ^ 2 * Q a`, so `Q (2jm) ≡ (2 P m ^ 2) ^ j`, a unit mod `Q m`
  because `Q m` is odd and coprime to `P m`.  Even multiples are therefore ruled out.

## Proved

* `pellQ_odd`, `pellQ_coprime_two_pellP_sq` — the arithmetic units used by the parity step;
* `pellQ_add_two_mul_modEq` — `Q (a + 2m) ≡ 2 P m ^ 2 * Q a [MOD Q m]`;
* `pellQ_even_multiple_modEq` — `Q (2jm) ≡ (2 P m ^ 2) ^ j [MOD Q m]`;
* `pellQ_coprime_even_multiple` — `gcd (Q m) (Q (2jm)) = 1`;
* `pellQ_dvd_index_dvd` — `Q m ∣ Q n → m ∣ n` for `m ≥ 2`;
* `pellQ_dvd_iff` — **the companion divisibility law**;
* `pellQ_gcd_dvd`, `pellQ_gcd_eq_one_of_even_quotient`, `pellQ_gcd_law` — **the companion
  gcd law**: `gcd (Q m) (Q n) = Q (gcd m n)` when both index quotients are odd, and `1`
  otherwise, with no side condition on `m` and `n`;
* `pellQ_gcd_of_odd_quotients` — the graded gcd statement that survives the refutation;
* summation identities `pellQ_sum`, `pellP_sum`, `pellP_sq_sum` tying the two strands
  of the spine together.

## Refuted

* `not_pellQ_dvd_all_multiples` — `Q n ∣ Q (kn)` fails for even `k`: `Q 2 = 3 ∤ 17 = Q 4`;
* `not_pellQ_dvd_iff_index_dvd` — divisibility of indices is **not** sufficient, by the
  same pair, so the parity grading in `pellQ_dvd_iff` cannot be dropped.
-/

open Catalog.Novelty.PellSpine

open Finset

/-! ## Arithmetic units modulo `Q m` -/



/-! ## The parity step -/




/-! ## The index step -/




/-! ## The companion divisibility law -/







/-! ## Refutations -/





/-! ## Summation identities linking the two strands -/





open Catalog.Novelty.PellSpine in
theorem solution(m j : ℕ) :
    pellQ (2 * j * m) ≡ (2 * pellP m ^ 2) ^ j [MOD pellQ m] := by
  induction j with
  | zero =>
      simp only [Nat.mul_zero, Nat.zero_mul, pow_zero]
      rfl
  | succ i ih =>
      have hidx : 2 * (i + 1) * m = 2 * i * m + 2 * m := by ring
      calc pellQ (2 * (i + 1) * m)
          = pellQ (2 * i * m + 2 * m) := by rw [hidx]
        _ ≡ 2 * pellP m ^ 2 * pellQ (2 * i * m) [MOD pellQ m] :=
            pellQ_add_two_mul_modEq m _
        _ ≡ 2 * pellP m ^ 2 * (2 * pellP m ^ 2) ^ i [MOD pellQ m] := ih.mul_left _
        _ = (2 * pellP m ^ 2) ^ (i + 1) := by ring
