-- Prove2me | Theorems.Thm_FibApparition_fib_apparition_exists
-- name    : FibApparition.fib_apparition_exists
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:52:26.383035+00:00
-- url     : https://prove2.me/theorems/307ba425-faf4-4b0c-a584-4b0241aac681
-- title:
--   Fib apparition exists
-- statement:
--   Formal statement of `FibApparition.fib_apparition_exists` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem FibApparition.fib_apparition_exists(m : ℕ) (hm : 0 < m) :
--       ∃ k, 0 < k ∧ m ∣ Nat.fib k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/Pythagorean/FibApparitionExistence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/Pythagorean/FibApparitionExistence.lean#L46

-- Thm stub generated from Applications/Pythagorean/FibApparitionExistence.lean
import Mathlib
import Definitions.Def_Applications_Pythagorean_FibApparitionExistence

/-!
# Existence and characterization of the Fibonacci rank of apparition

For a modulus `m ≥ 1`, the *rank of apparition* `z(m)` is the least positive index `k`
with `m ∣ F k`.  The catalog already contains the *one-directional* divisibility lemma
(`fibEntryPt_dvd_of_fib_dvd` in `Speculative.AutoResearch.CarmichaelComposite`),
which assumes the apparition exists and requires `m` to be prime.

This file **extends** that work in two directions:

* `fib_apparition_exists` — for *every* modulus `m ≥ 1` (not just primes) the rank of
  apparition exists.  This is the genuinely new, harder ingredient: it is proved by a
  finiteness / pigeonhole argument on the Fibonacci shift map over `ZMod m`, which is the
  abstract reason behind the Pisano period.  Mathlib has no Pisano-period theory, so this
  is built from scratch.
* `fib_dvd_iff_apparition_dvd` — the full **biconditional** `m ∣ F n ↔ z ∣ n`, valid for
  any modulus, strengthening the catalog's single implication.

Combining them, `fib_dvd_iff_apparitionRank_dvd` gives, for every `m ≥ 1`, a clean
characterization `m ∣ F n ↔ z(m) ∣ n` where `z(m)` is defined unconditionally.
-/

open FibApparition

open scoped Classical


-- !-- Iterating the shift map from `(0,1)` produces consecutive Fibonacci pairs;
-- proved by induction on `k` using the recurrence `F (k+2) = F k + F (k+1)`. -- !--

-- !-- The shift map is a permutation of the finite set `ZMod m × ZMod m`, so its orbit
-- through `(0,1)` repeats: pigeonhole gives `i < j` with equal iterates, and injectivity
-- of the iterates yields a positive `k = j - i` with `(F k, F (k+1)) ≡ (0,1)`, i.e. `m ∣ F k`. -- !--

theorem FibApparition.fib_apparition_exists(m : ℕ) (hm : 0 < m) :
    ∃ k, 0 < k ∧ m ∣ Nat.fib k := by sorry
