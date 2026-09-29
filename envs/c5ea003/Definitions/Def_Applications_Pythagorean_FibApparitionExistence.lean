-- Prove2me | Definitions.Def_Applications_Pythagorean_FibApparitionExistence
-- name    : Applications_Pythagorean_FibApparitionExistence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:27.910371+00:00
-- url     : https://prove2.me/theorems/c5873c34-e93c-47b7-99b8-e205671ada29
-- title:
--   Aether Catalog definitions — Applications_Pythagorean_FibApparitionExistence
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Pythagorean.FibApparitionExistence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Pythagorean/FibApparitionExistence.lean by skeleton subtraction
import Mathlib

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

namespace FibApparition

open scoped Classical

/-- The Fibonacci "shift" permutation on pairs over `ZMod m`:
`(a, b) ↦ (b, a + b)`, with inverse `(a, b) ↦ (b - a, a)`. -/
def fibStep (m : ℕ) : ZMod m × ZMod m ≃ ZMod m × ZMod m where
  toFun p := (p.2, p.1 + p.2)
  invFun p := (p.2 - p.1, p.1)
  left_inv := by intro p; simp
  right_inv := by intro p; simp [add_comm]

-- !-- Iterating the shift map from `(0,1)` produces consecutive Fibonacci pairs;
-- proved by induction on `k` using the recurrence `F (k+2) = F k + F (k+1)`. -- !--

-- !-- The shift map is a permutation of the finite set `ZMod m × ZMod m`, so its orbit
-- through `(0,1)` repeats: pigeonhole gives `i < j` with equal iterates, and injectivity
-- of the iterates yields a positive `k = j - i` with `(F k, F (k+1)) ≡ (0,1)`, i.e. `m ∣ F k`. -- !--

-- !-- Biconditional rank-of-apparition law.  Backward: `z ∣ n → F z ∣ F n → m ∣ F n`
-- via `Nat.fib_dvd`.  Forward: `m ∣ gcd (F z) (F n) = F (gcd z n)` by `Nat.fib_gcd`;
-- minimality of `z` forces `gcd z n = z`, hence `z ∣ n`. -- !--

/-- The Fibonacci rank of apparition of `m`: the least positive `k` with `m ∣ F k`
(or `0` if none exists; for `m ≥ 1` existence is guaranteed by `fib_apparition_exists`). -/
noncomputable def apparitionRank (m : ℕ) : ℕ :=
  if h : ∃ k, 0 < k ∧ m ∣ Nat.fib k then Nat.find h else 0



-- !-- Capstone: combine unconditional existence with the biconditional law to obtain a
-- clean divisibility characterization for every modulus `m ≥ 1`. -- !--

end FibApparition


