-- Prove2me | Definitions.Def_Novelty_BinomialGCDFRange
-- name    : Novelty_BinomialGCDFRange
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:07:27.960971+00:00
-- url     : https://prove2.me/theorems/567143ad-f3fa-43df-a645-3cb9633a5eac
-- title:
--   Aether Catalog definitions — Novelty_BinomialGCDFRange
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.BinomialGCDFRange`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/BinomialGCDFRange.lean by skeleton subtraction
import Mathlib

/-!
# The Pascal-row interior GCD and prime powers

For `k ≥ 1` put `n = k + 1` and let
`F(k) = gcd_{1 ≤ i ≤ k} C(n, i)`
be the gcd of the *interior* entries of row `n` of Pascal's triangle.

This is the classical "Ram" gcd: `F(k) = p` when `n = p^a` is a prime power,
and `F(k) = 1` otherwise.  This file records the corrected qualitative
statement

* `F_eq_one_iff` — for `k ≥ 1`, `F k = 1 ↔ ¬ IsPrimePow (k + 1)`.

The forward direction is the contrapositive of `F_ne_one_of_succ_primePow`
(itself built on `primepower_succ_dvd_F`, which divides every interior binomial
of a prime-power row by the underlying prime via `Nat.Prime.dvd_choose_pow`).
The backward direction is the genuine arithmetic content: if `n` is *not* a
prime power then for every prime `p ∣ n`, taking `i = p^{v_p(n)}` gives an
interior binomial `C(n, i)` not divisible by `p` (Kummer: no carries), so no
prime divides `F k`, whence `F k = 1`.
-/

namespace BinomialGCDFRange

open Nat Finset

/-- `F(k) = gcd_{1 ≤ i ≤ k} C(k+1, i)`, the gcd of the interior entries of row
`k+1` of Pascal's triangle. -/
def F (k : ℕ) : ℕ := (Finset.Icc 1 k).gcd (fun i => Nat.choose (k + 1) i)


/-
**Forward (prime-power) divisibility.**  If `k + 1 = p ^ a` is a prime
power then the prime `p` divides every interior binomial of the row, hence
`p ∣ F k`.
-/

/-
**Forward conclusion.**  If `k + 1` is a prime power then `F k ≠ 1`.
-/

/-
**Key arithmetic lemma (Kummer / no carries).**  For a prime `p` and any
`m` not divisible by `p`, the prime `p` does not divide `C(p^a · m, p^a)`.
(Adding `p^a` and `p^a·(m-1)` in base `p` produces no carry because the digit
of `m` at position `a` — namely `m mod p` — is nonzero.)
-/

/-
**Backward direction.**  If `k ≥ 1` and `k + 1` is not a prime power then
`F k = 1`.
-/


end BinomialGCDFRange


