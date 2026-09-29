-- Prove2me | Definitions.Def_Applications_Pythagorean_UnifiedRankOfApparition
-- name    : Applications_Pythagorean_UnifiedRankOfApparition
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:36.447258+00:00
-- url     : https://prove2.me/theorems/6a758cb0-5fc4-4df8-aff2-7be8f123c99e
-- title:
--   Aether Catalog definitions — Applications_Pythagorean_UnifiedRankOfApparition
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Pythagorean.UnifiedRankOfApparition`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Pythagorean/UnifiedRankOfApparition.lean by skeleton subtraction
import Mathlib

/-! # The rank-of-apparition engine for arbitrary strong divisibility sequences

Domain: Number Theory / Applications (Conceptual Unification).

The catalog contains two parallel developments of the *rank of apparition* idea:

* `Catalog/Applications/RankOfApparition.lean` builds the rank function `fibRank`, the spine
  `fibRank_dvd_iff : m ∣ F n ↔ fibRank m ∣ n`, the order-morphism law `fibRank_dvd_of_dvd`,
  the rigidity `fibRank_fib : fibRank (F k) = k`, and the Fibonacci divisibility biconditional
  `fib_dvd_fib_iff : F a ∣ F b ↔ a ∣ b` — but *only* for the Fibonacci sequence.
* `Catalog/Applications/StrongDivisibilitySequences.lean` introduces the abstract notion
  `IsStrongDivSeq u : u (gcd m n) = gcd (u m) (u n)` together with the primitivity theory
  (`isPrimitive_unique`, `dvd_iff_index_dvd_of_primitive`, `simultaneous_apparition`, …) and
  the two concrete instances `fib_isStrongDivSeq` and `mersenne_isStrongDivSeq` (`n ↦ aⁿ − 1`),
  but it never builds a *rank function* and never proves the value biconditional `u a ∣ u b ↔ a ∣ b`.

This file **unifies the two**: it lifts the entire rank machinery of `RankOfApparition` from
`Nat.fib` to an arbitrary strong divisibility sequence, proving the generic spine
`rank_dvd_iff`, the order morphism `rank_dvd_of_dvd`, the rigidity `rank_self`, and the value
biconditional `value_dvd_iff` from the single hypothesis `IsStrongDivSeq u`.  Two classical
theorems then drop out as *instances of one engine*:

* `fib_dvd_fib_iff`     — `F a ∣ F b ↔ a ∣ b` for `a ≥ 3` (recovering `RankOfApparition`);
* `mersenne_dvd_iff`    — `(aᵐ − 1) ∣ (aⁿ − 1) ↔ m ∣ n` for `a ≥ 2`, `m ≥ 1` (**new**: the
  classical Mersenne divisibility law, which the catalog stated the SDS instance for but never
  derived the index biconditional of).

This is a Grothendieck-style unification: the gcd-meet law `IsStrongDivSeq` *is* the abstract
"Pisano/order" mechanism, and Fibonacci vs. `aⁿ−1` are two specializations of one truth.
-/

namespace UnifiedRank

open scoped Classical

/-- A **strong divisibility sequence**: `u (gcd m n) = gcd (u m) (u n)` for all `m, n`.
(Same notion as `StrongDivSeq.IsStrongDivSeq`; restated here so the file is self-contained
against the catalog's fragmented import graph.) -/
def IsStrongDivSeq (u : ℕ → ℕ) : Prop :=
  ∀ m n, u (Nat.gcd m n) = Nat.gcd (u m) (u n)

/-! ## §1. The weak divisibility law -/

-- !-- Lab Notebook: IsStrongDivSeq.dvd_of_dvd -- !--
-- !-- Hypothesis: a strong divisibility sequence is a divisibility sequence: `m ∣ n → u m ∣ u n`. -- !--
-- !-- Result: `m ∣ n` gives `gcd m n = m`, so `u m = u (gcd m n) = gcd (u m) (u n) ∣ u n`. -- !--
-- !-- Insight: the weak law is a free corollary of the strong (meet) law. -- !--
-- !-- Failure analysis: none. -- !--
-- !-- End Lab Notebook -- !--

/-! ## §2. The rank function -/

/-- `m` *has a rank of apparition* for `u` if it divides some positive-index value `u k`. -/
def HasRank (u : ℕ → ℕ) (m : ℕ) : Prop := ∃ k, 0 < k ∧ m ∣ u k

/-- The rank of apparition of `m` in `u`: the least positive `k` with `m ∣ u k`
(or `0` if none exists). -/
noncomputable def rank (u : ℕ → ℕ) (m : ℕ) : ℕ :=
  if h : ∃ k, 0 < k ∧ m ∣ u k then Nat.find h else 0




/-! ## §3. The spine: `m ∣ u n ↔ rank u m ∣ n` -/

-- !-- Lab Notebook: rank_dvd_iff -- !--
-- !-- Hypothesis: for any modulus with a rank, `m ∣ u n ↔ rank u m ∣ n` (generic spine). -- !--
-- !-- Result: (←) `rank ∣ n → u(rank) ∣ u n` (weak law) plus `m ∣ u(rank)`. (→) push `m` into
-- the meet law `u (gcd (rank) n) = gcd (u rank) (u n)`; minimality of the rank forces
-- `gcd (rank) n = rank`, i.e. `rank ∣ n`. -- !--
-- !-- Insight: this generalizes `RankOfApparition.fibRank_dvd_iff` from `Nat.fib_gcd` to the
-- bare `IsStrongDivSeq` hypothesis — the load-bearing fact of all apparition threads. -- !--
-- !-- Failure analysis: needs `HasRank u m` for positivity of the rank. -- !--
-- !-- End Lab Notebook -- !--

/-! ## §4. The order-morphism law (with existence) -/

-- !-- Lab Notebook: rank_dvd_of_dvd -- !--
-- !-- Hypothesis: `rank` is an order morphism of divisibility posets: `b ∣ a → rank b ∣ rank a`. -- !--
-- !-- Result: from the spine: `b ∣ a ∣ u (rank a)`, so `b ∣ u (rank a)`, and the spine for `b`
-- gives `rank b ∣ rank a`. -- !--
-- !-- Insight: monotonicity packaged with existence of the divisor's rank. -- !--
-- !-- Failure analysis: needs a totality witness `hex` so that `a, b` have ranks. -- !--
-- !-- End Lab Notebook -- !--

/-! ## §5. Rigidity: the rank pins the values exactly -/

-- !-- Lab Notebook: rank_self -- !--
-- !-- Hypothesis: if `u` is positive and strictly grows up to index `k`, then `rank u (u k) = k`. -- !--
-- !-- Result: `Nat.find_eq_iff`: `u k ∣ u k` trivially, and for `0 < j < k` we have
-- `0 < u j < u k`, so `u k ∤ u j` (`Nat.not_dvd_of_pos_of_lt`). -- !--
-- !-- Insight: the abstract version of `RankOfApparition.fibRank_fib`; growth replaces the
-- Fibonacci-specific monotonicity. -- !--
-- !-- Failure analysis: needs strict growth strictly below `k`; equal values (e.g. `F 1 = F 2`)
-- break it, which is exactly why Fibonacci needed `k ≥ 3`. -- !--
-- !-- End Lab Notebook -- !--

/-! ## §6. The value biconditional -/

-- !-- Lab Notebook: value_dvd_iff -- !--
-- !-- Hypothesis: under positivity + growth at `a`, `u a ∣ u b ↔ a ∣ b`. -- !--
-- !-- Result: `rank u (u a) = a` (rank_self), then spine `u a ∣ u b ↔ rank u (u a) ∣ b ↔ a ∣ b`. -- !--
-- !-- Insight: the spine converts a statement about values into one about indices, upgrading
-- the weak law `dvd_of_dvd` to a biconditional in one stroke. -- !--
-- !-- Failure analysis: growth strictly below `a` is required (sharp). -- !--
-- !-- End Lab Notebook -- !--

/-! ## §7. Instance I — Fibonacci -/

-- !-- Fibonacci is a strong divisibility sequence by `Nat.fib_gcd`. -- !--

-- !-- Lab Notebook: fib_dvd_fib_iff -- !--
-- !-- Hypothesis: `F a ∣ F b ↔ a ∣ b` for `a ≥ 3` (recovering RankOfApparition via the engine). -- !--
-- !-- Result: instance of `value_dvd_iff` with `u = Nat.fib`; positivity is `Nat.fib_pos`,
-- growth `F j < F a` for `0 < j < a, a ≥ 3` from `F j ≤ F (a-1) < F a`. -- !--
-- !-- Insight: the classical Fibonacci biconditional is now a one-line instance of a generic engine. -- !--
-- !-- Failure analysis: `a = 1, 2` break it (`F 1 = F 2 = 1`); `a ≥ 3` is sharp. -- !--
-- !-- End Lab Notebook -- !--

/-! ## §8. Instance II — Mersenne / `aⁿ − 1` (cross-domain corollary) -/

-- !-- The Mersenne sequence `n ↦ aⁿ − 1` is a strong divisibility sequence. -- !--

-- !-- Lab Notebook: mersenne_dvd_iff -- !--
-- !-- Hypothesis: `(aᵐ − 1) ∣ (aⁿ − 1) ↔ m ∣ n` for `a ≥ 2`, `m ≥ 1` (the classical Mersenne law). -- !--
-- !-- Result: instance of `value_dvd_iff` with `u = (· ↦ aⁿ − 1)`; positivity from `1 < aʲ`,
-- growth from strict monotonicity of `a ^ ·` for base `≥ 2`. -- !--
-- !-- Insight: the SAME engine that yields the Fibonacci biconditional yields the Mersenne one —
-- a genuine cross-domain bridge (number theory of `aⁿ−1` ↔ Fibonacci) through `IsStrongDivSeq`. -- !--
-- !-- Failure analysis: `a ≤ 1` collapses the sequence; `m = 0` gives `a⁰ − 1 = 0 ∣ everything`. -- !--
-- !-- End Lab Notebook -- !--

end UnifiedRank


