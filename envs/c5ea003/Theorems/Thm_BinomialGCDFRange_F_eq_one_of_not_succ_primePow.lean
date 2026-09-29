-- Prove2me | Theorems.Thm_BinomialGCDFRange_F_eq_one_of_not_succ_primePow
-- name    : BinomialGCDFRange.F_eq_one_of_not_succ_primePow
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:05:50.513234+00:00
-- url     : https://prove2.me/theorems/b75f2e1e-20e1-4997-b390-33966e645ef5
-- title:
--   F eq one of not succ primePow
-- statement:
--   Formal statement of `BinomialGCDFRange.F_eq_one_of_not_succ_primePow` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem BinomialGCDFRange.F_eq_one_of_not_succ_primePow{k : ℕ} (hk : 1 ≤ k)
--       (h : ¬ IsPrimePow (k + 1)) : F k = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BinomialGCDFRange.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BinomialGCDFRange.lean#L77

-- Thm stub generated from Novelty/BinomialGCDFRange.lean
import Mathlib
import Definitions.Def_Novelty_BinomialGCDFRange

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

open BinomialGCDFRange

open Nat Finset



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

theorem BinomialGCDFRange.F_eq_one_of_not_succ_primePow{k : ℕ} (hk : 1 ≤ k)
    (h : ¬ IsPrimePow (k + 1)) : F k = 1 := by sorry
