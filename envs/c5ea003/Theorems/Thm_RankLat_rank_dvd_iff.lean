-- Prove2me | Theorems.Thm_RankLat_rank_dvd_iff
-- name    : RankLat.rank_dvd_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:01:25.188685+00:00
-- url     : https://prove2.me/theorems/176d85f0-20c8-4961-a272-08043836c2f3
-- title:
--   Rank dvd iff
-- statement:
--   Formal statement of `RankLat.rank_dvd_iff` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RankLat.rank_dvd_iff{u : ℕ → ℕ} (hu : IsStrongDivSeq u) {m : ℕ} (hm : HasRank u m) (n : ℕ) :
--       m ∣ u n ↔ rank u m ∣ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/Pythagorean/RankLatticeMorphism.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/Pythagorean/RankLatticeMorphism.lean#L83

-- Thm stub generated from Applications/Pythagorean/RankLatticeMorphism.lean
import Mathlib
import Definitions.Def_Applications_Pythagorean_RankLatticeMorphism

/-! # The rank of apparition is a lattice (lcm-)morphism

Domain: Number Theory / Applications (Conceptual Unification).

This file extends the *rank of apparition* engine developed in the catalog
(`Catalog/Applications/RankOfApparition.lean` and
`Catalog/Applications/UnifiedRankOfApparition.lean`).  Those files build, for an arbitrary
**strong divisibility sequence** `u` (one with `u (gcd m n) = gcd (u m) (u n)`), the rank
function `rank u`, the *spine* `rank_dvd_iff : m ∣ u n ↔ rank u m ∣ n`, the order-morphism
law `rank_dvd_of_dvd`, the rigidity `rank_self`, and the value biconditionals for Fibonacci
(`F a ∣ F b ↔ a ∣ b`) and Mersenne (`aᵐ−1 ∣ aⁿ−1 ↔ m ∣ n`).

What was *missing* from every catalog thread is the **join law**: how the rank interacts with
`lcm` on the modulus side.  The catalog only ever proved the order-morphism law
(`b ∣ a → rank b ∣ rank a`), i.e. that `rank` is *monotone* for divisibility.  Here we prove
the sharp structural statement that `rank` is in fact a **homomorphism of join-semilattices**
`(ℕ_{>0}, lcm) → (ℕ_{>0}, lcm)`:

* `rank_lcm`           — *new, generic*: `rank u (lcm a b) = lcm (rank u a) (rank u b)`,
  from the bare `IsStrongDivSeq` hypothesis and existence of `rank u a`, `rank u b`
  (existence of the rank of `lcm a b` is *derived*, `hasRank_lcm`, not assumed).
* `rank_mul_coprime`   — *new corollary*: for coprime `a, b`,
  `rank u (a * b) = lcm (rank u a) (rank u b)` (the multiplicative entry-point law).
* `fibRank_lcm`        — *new instance*: `rank F (lcm a b) = lcm (rank F a) (rank F b)` for
  `a, b ≥ 1` (the classical *Fibonacci entry point of an lcm*; totality comes from the
  Pisano pigeonhole `fib_hasRank`, copied from `RankOfApparition`).
* `mersenne_rank_lcm`  — *new cross-domain instance*: in the Mersenne sequence `k ↦ aᵏ − 1`,
  `rank (lcm (aᵐ−1) (aⁿ−1)) = lcm m n` for `a ≥ 2`, `m, n ≥ 1`.

The point is conceptual: the **same** join law specialises to Fibonacci and to `aⁿ−1`, two
sequences with no surface resemblance, because both are strong divisibility sequences.  This
is the lattice-theoretic core of the "Law of Apparition" duality flagged in the catalog's
`FUTURE_DIRECTIONS` synthesis.

The file is self-contained against Mathlib (the catalog's `import` graph is fragmented), so it
restates the small engine core it uses, in the established style of the catalog.
-/

open RankLat

open scoped Classical


-- !-- A strong divisibility sequence is a divisibility sequence:
-- !-- `m ∣ n` gives `gcd m n = m`, so `u m = gcd (u m) (u n) ∣ u n`. -- !--

/-! ## §1. The rank function (engine core, restated) -/






-- !-- The spine `m ∣ u n ↔ rank u m ∣ n`: (←) weak law + `m ∣ u(rank)`; (→) push `m` into the
-- !-- meet law and use minimality of the rank to force `gcd (rank) n = rank`. -- !--

theorem RankLat.rank_dvd_iff{u : ℕ → ℕ} (hu : IsStrongDivSeq u) {m : ℕ} (hm : HasRank u m) (n : ℕ) :
    m ∣ u n ↔ rank u m ∣ n := by sorry
