-- Prove2me | solution 1 for RankLat.fib_hasRank
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:07:09.021571+00:00
-- url     : https://prove2.me/submissions/aaa20dda-202f-401c-92d2-1565c1d11e26

-- Sol generated from Applications/Pythagorean/RankLatticeMorphism.lean
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

-- !-- Rigidity `rank u (u k) = k` under positivity + strict growth below `k`
-- !-- (`Nat.find_eq_iff`: `u k ∣ u k`; for `0 < j < k`, `0 < u j < u k` blocks division). -- !--

/-! ## §2. NEW — existence of the rank of an lcm -/

/-
!-- Lab Notebook: hasRank_lcm -- !--
!-- Hypothesis: If `a` and `b` both have ranks for `u`, then so does `lcm a b` — no global
totality assumption needed. -- !--
!-- Result: Proved. Let `k = lcm (rank a) (rank b)`. Since `rank a ∣ k`, the weak law gives
`a ∣ u(rank a) ∣ u k`; symmetrically `b ∣ u k`; hence `lcm a b ∣ u k`, and `k > 0`. -- !--
!-- Insight: existence of ranks is closed under `lcm`, so the join law `rank_lcm` never has to
postulate the rank of the join — it manufactures the witness from the two given ranks. -- !--
!-- Failure analysis: needs the weak law `dvd_of_dvd`, i.e. that `u` is a divisibility
sequence (a free consequence of `IsStrongDivSeq`). -- !--
!-- End Lab Notebook -- !--
-/

/-! ## §3. NEW — the join (lcm-)morphism law -/

/-
!-- Lab Notebook: rank_lcm -- !--
!-- Hypothesis: `rank` is a join-semilattice morphism for divisibility:
`rank u (lcm a b) = lcm (rank u a) (rank u b)`. -- !--
!-- Result: Proved by divisibility-antisymmetry, all four legs via the spine + `Nat.lcm_dvd`.
`r ∣ L`: `lcm a b ∣ u L` because `a ∣ u L` and `b ∣ u L` (spine: `rank a ∣ L`, `rank b ∣ L`),
then spine for `lcm a b`. `L ∣ r`: `rank a ∣ r` and `rank b ∣ r` because `a, b ∣ lcm a b ∣ u r`
(spine again). -- !--
!-- Insight: This upgrades the catalog's *monotone* order-morphism `rank_dvd_of_dvd` to a full
*join homomorphism*. Both ranks `r` and `L` cut out the exact same principal ideal of indices,
so the spine forces them equal — the load-bearing structural fact of apparition. -- !--
!-- Failure analysis: the dual `gcd` law fails in general (gcd of the moduli need not have rank
gcd of the ranks), so only the join law holds — a genuine asymmetry, not an oversight. -- !--
!-- End Lab Notebook -- !--
-/

/-
!-- Lab Notebook: rank_mul_coprime -- !--
!-- Hypothesis: for coprime `a, b`, `rank u (a * b) = lcm (rank u a) (rank u b)`. -- !--
!-- Result: Proved. Coprimality gives `lcm a b = a * b` (`Nat.Coprime.lcm_eq_mul`), so this is
`rank_lcm` rewritten. -- !--
!-- Insight: the multiplicative entry-point law (e.g. the classical formula for the Fibonacci
entry point of a coprime product) is a one-line corollary of the join morphism. -- !--
!-- Failure analysis: coprimality is essential; without it `lcm a b ≠ a * b`. -- !--
!-- End Lab Notebook -- !--
-/

/-! ## §4. Instance I — Fibonacci -/


-- !-- Lab Notebook: fib_hasRank -- !--
-- !-- Hypothesis: every positive modulus has a Fibonacci rank (apparition is total). -- !--
-- !-- Result: pigeonhole on the finite `(ZMod m)²`; back-step a repeated pair to `(0,1)` via
-- the reversible shift to get `0 < k` with `m ∣ F k`. (Copied from `RankOfApparition`.) -- !--
-- !-- Insight: totality is what lets `fibRank_lcm` quantify over all positive `a, b`. -- !--
-- !-- Failure analysis: the `m = 0` `ZMod` case is split off. -- !--
-- !-- End Lab Notebook -- !--

-- !-- Fibonacci is a strong divisibility sequence by `Nat.fib_gcd`. -- !--

/-
!-- Lab Notebook: fibRank_lcm -- !--
!-- Hypothesis: `rank F (lcm a b) = lcm (rank F a) (rank F b)` for all `a, b ≥ 1`
(the Fibonacci entry point of an lcm). -- !--
!-- Result: instance of `rank_lcm` with `u = Nat.fib`; ranks exist by `fib_hasRank`. -- !--
!-- Insight: the classical "entry point of lcm is lcm of entry points" is now a one-line
specialisation of the generic join morphism. -- !--
!-- Failure analysis: needs `a, b ≥ 1` for totality. -- !--
!-- End Lab Notebook -- !--
-/

/-! ## §5. Instance II — Mersenne / `aⁿ − 1` (cross-domain corollary) -/

-- !-- The Mersenne sequence `n ↦ aⁿ − 1` is a strong divisibility sequence. -- !--

-- !-- Lab Notebook: mersenne_rank_value -- !--
-- !-- Hypothesis: `rank (·↦ aᵏ−1) (aᵏ−1) = k` for `a ≥ 2`, `k ≥ 1`. -- !--
-- !-- Result: instance of `rank_self`; positivity `1 < aʲ` and strict growth from
-- `Nat.pow_lt_pow_right`. -- !--
-- !-- Insight: each Mersenne value is rank-rigid, so the lcm law reads off the indices. -- !--
-- !-- Failure analysis: `a ≤ 1` collapses the sequence; `k = 0` gives `a⁰−1 = 0`. -- !--
-- !-- End Lab Notebook -- !--

/-
!-- Lab Notebook: mersenne_rank_lcm -- !--
!-- Hypothesis: `rank (·↦ aᵏ−1) (lcm (aᵐ−1) (aⁿ−1)) = lcm m n` for `a ≥ 2`, `m, n ≥ 1`. -- !--
!-- Result: `rank_lcm` for the Mersenne SDS, with the two ranks computed by
`mersenne_rank_value`. -- !--
!-- Insight: the SAME join law that gives the Fibonacci lcm-entry-point gives the Mersenne one —
a genuine cross-domain bridge through `IsStrongDivSeq`, with no growth/Pisano theory in common. -- !--
!-- Failure analysis: `a ≤ 1` or `m = 0`/`n = 0` break rank-rigidity. -- !--
!-- End Lab Notebook -- !--
-/


open RankLat in
theorem solution{m : ℕ} (hm : 0 < m) : HasRank Nat.fib m := by
  obtain ⟨i, j, hij, h_pair⟩ :
      ∃ i j : ℕ, i < j ∧
        ((Nat.fib i : ZMod m) = (Nat.fib j : ZMod m) ∧
          (Nat.fib (i + 1) : ZMod m) = (Nat.fib (j + 1) : ZMod m)) := by
    have h_pigeonhole :
        ∃ i j : ℕ, i < j ∧
          ((Nat.fib i : ZMod m), (Nat.fib (i + 1) : ZMod m))
            = ((Nat.fib j : ZMod m), (Nat.fib (j + 1) : ZMod m)) := by
      by_contra! h
      have h_finite :
          Set.Finite (Set.range
            (fun n : ℕ => ((Nat.fib n : ZMod m), (Nat.fib (n + 1) : ZMod m)))) := by
        cases m <;> [ aesop; exact Set.toFinite _ ]
      exact h_finite.not_infinite <| Set.infinite_range_of_injective fun i j hij =>
        le_antisymm (le_of_not_gt fun hi => h _ _ hi hij.symm)
          (le_of_not_gt fun hj => h _ _ hj hij)
    aesop
  induction' i with i ih generalizing j
  · exact ⟨ j, hij, by simpa [ ← ZMod.natCast_eq_zero_iff ] using h_pair.1.symm ⟩
  · specialize ih ( j - 1 ) ( Nat.lt_pred_iff.mpr hij )
    rcases j <;> simp_all +decide [ Nat.fib_add_two ]
    grind
