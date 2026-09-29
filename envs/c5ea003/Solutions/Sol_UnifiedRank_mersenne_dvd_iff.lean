-- Prove2me | solution 1 for UnifiedRank.mersenne_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:51:31.114617+00:00
-- url     : https://prove2.me/submissions/ae49e47b-a7ab-4aed-b83d-4c1b0ea31acd

-- Sol generated from Applications/Pythagorean/UnifiedRankOfApparition.lean
import Mathlib
import Definitions.Def_Applications_Pythagorean_UnifiedRankOfApparition
import Theorems.Thm_UnifiedRank_rank_dvd_iff

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

open UnifiedRank

open scoped Classical


/-! ## §1. The weak divisibility law -/

-- !-- Lab Notebook: IsStrongDivSeq.dvd_of_dvd -- !--
-- !-- Hypothesis: a strong divisibility sequence is a divisibility sequence: `m ∣ n → u m ∣ u n`. -- !--
-- !-- Result: `m ∣ n` gives `gcd m n = m`, so `u m = u (gcd m n) = gcd (u m) (u n) ∣ u n`. -- !--
-- !-- Insight: the weak law is a free corollary of the strong (meet) law. -- !--
-- !-- Failure analysis: none. -- !--
-- !-- End Lab Notebook -- !--

/-! ## §2. The rank function -/






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
theorem rank_self {u : ℕ → ℕ} {k : ℕ} (hk : 0 < k)
    (hpos : ∀ j, 0 < j → 0 < u j)
    (hgrow : ∀ j, 0 < j → j < k → u j < u k) :
    rank u (u k) = k := by
  have hhas : ∃ j, 0 < j ∧ u k ∣ u j := ⟨k, hk, dvd_rfl⟩
  unfold rank
  rw [dif_pos hhas, Nat.find_eq_iff]
  refine ⟨⟨hk, dvd_rfl⟩, ?_⟩
  intro j hj hcontra
  obtain ⟨hj0, hdvd⟩ := hcontra
  exact Nat.not_dvd_of_pos_of_lt (hpos j hj0) (hgrow j hj0 hj) hdvd

/-! ## §6. The value biconditional -/

-- !-- Lab Notebook: value_dvd_iff -- !--
-- !-- Hypothesis: under positivity + growth at `a`, `u a ∣ u b ↔ a ∣ b`. -- !--
-- !-- Result: `rank u (u a) = a` (rank_self), then spine `u a ∣ u b ↔ rank u (u a) ∣ b ↔ a ∣ b`. -- !--
-- !-- Insight: the spine converts a statement about values into one about indices, upgrading
-- the weak law `dvd_of_dvd` to a biconditional in one stroke. -- !--
-- !-- Failure analysis: growth strictly below `a` is required (sharp). -- !--
-- !-- End Lab Notebook -- !--
theorem value_dvd_iff {u : ℕ → ℕ} (hu : IsStrongDivSeq u) {a b : ℕ} (ha : 0 < a)
    (hpos : ∀ j, 0 < j → 0 < u j)
    (hgrow : ∀ j, 0 < j → j < a → u j < u a) :
    u a ∣ u b ↔ a ∣ b := by
  have hhas : HasRank u (u a) := ⟨a, ha, dvd_rfl⟩
  have hrk : rank u (u a) = a := rank_self ha hpos hgrow
  rw [rank_dvd_iff hu hhas b, hrk]

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
theorem mersenne_isStrongDivSeq (a : ℕ) : IsStrongDivSeq (fun n => a ^ n - 1) := by
  intro m n
  by_cases ha : a = 0 <;> simp_all +decide [Nat.pow_sub_one_gcd_pow_sub_one]

-- !-- Lab Notebook: mersenne_dvd_iff -- !--
-- !-- Hypothesis: `(aᵐ − 1) ∣ (aⁿ − 1) ↔ m ∣ n` for `a ≥ 2`, `m ≥ 1` (the classical Mersenne law). -- !--
-- !-- Result: instance of `value_dvd_iff` with `u = (· ↦ aⁿ − 1)`; positivity from `1 < aʲ`,
-- growth from strict monotonicity of `a ^ ·` for base `≥ 2`. -- !--
-- !-- Insight: the SAME engine that yields the Fibonacci biconditional yields the Mersenne one —
-- a genuine cross-domain bridge (number theory of `aⁿ−1` ↔ Fibonacci) through `IsStrongDivSeq`. -- !--
-- !-- Failure analysis: `a ≤ 1` collapses the sequence; `m = 0` gives `a⁰ − 1 = 0 ∣ everything`. -- !--
-- !-- End Lab Notebook -- !--


open UnifiedRank in
theorem solution{a m n : ℕ} (ha : 2 ≤ a) (hm : 0 < m) :
    (a ^ m - 1) ∣ (a ^ n - 1) ↔ m ∣ n := by
  have key := value_dvd_iff (mersenne_isStrongDivSeq a) (a := m) (b := n) hm
    (by
      intro j hj
      have : 1 < a ^ j := Nat.one_lt_pow (by omega) (by omega)
      omega)
    (by
      intro j hj0 hj
      have h1 : a ^ j < a ^ m := Nat.pow_lt_pow_right (by omega) hj
      have h2 : 0 < a ^ j := Nat.pow_pos (by omega)
      omega)
  simpa using key
