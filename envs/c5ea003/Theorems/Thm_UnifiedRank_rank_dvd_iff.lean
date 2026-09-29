-- Prove2me | Theorems.Thm_UnifiedRank_rank_dvd_iff
-- name    : UnifiedRank.rank_dvd_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:07:13.295682+00:00
-- url     : https://prove2.me/theorems/16734f24-e4fd-42fa-b35d-6d468541c943
-- title:
--   Rank dvd iff
-- statement:
--   Formal statement of `UnifiedRank.rank_dvd_iff` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem UnifiedRank.rank_dvd_iff{u : ℕ → ℕ} (hu : IsStrongDivSeq u) {m : ℕ} (hm : HasRank u m) (n : ℕ) :
--       m ∣ u n ↔ rank u m ∣ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/Pythagorean/UnifiedRankOfApparition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/Pythagorean/UnifiedRankOfApparition.lean#L96

-- Thm stub generated from Applications/Pythagorean/UnifiedRankOfApparition.lean
import Mathlib
import Definitions.Def_Applications_Pythagorean_UnifiedRankOfApparition

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

theorem UnifiedRank.rank_dvd_iff{u : ℕ → ℕ} (hu : IsStrongDivSeq u) {m : ℕ} (hm : HasRank u m) (n : ℕ) :
    m ∣ u n ↔ rank u m ∣ n := by sorry
