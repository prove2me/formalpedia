-- Prove2me | solution 1 for FibApparition.fib_apparition_exists
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:15:46.949367+00:00
-- url     : https://prove2.me/submissions/18e9fa48-0243-4d84-975a-f2132f98e6c3

-- Sol generated from Applications/Pythagorean/FibApparitionExistence.lean
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

-- !-- Biconditional rank-of-apparition law.  Backward: `z ∣ n → F z ∣ F n → m ∣ F n`
-- via `Nat.fib_dvd`.  Forward: `m ∣ gcd (F z) (F n) = F (gcd z n)` by `Nat.fib_gcd`;
-- minimality of `z` forces `gcd z n = z`, hence `z ∣ n`. -- !--




-- !-- Capstone: combine unconditional existence with the biconditional law to obtain a
-- clean divisibility characterization for every modulus `m ≥ 1`. -- !--


open FibApparition in
theorem solution(m : ℕ) (hm : 0 < m) :
    ∃ k, 0 < k ∧ m ∣ Nat.fib k := by
  -- By the pigeonhole principle, since there are only $m^2$ possible pairs $(F_k \mod m, F_{k+1} \mod m)$, there must exist indices $i < j$ such that $(F_i \mod m, F_{i+1} \mod m) = (F_j \mod m, F_{j+1} \mod m)$.
  obtain ⟨i, j, hij, h_pair⟩ : ∃ i j : ℕ, i < j ∧ ((Nat.fib i : ZMod m) = (Nat.fib j : ZMod m) ∧ (Nat.fib (i + 1) : ZMod m) = (Nat.fib (j + 1) : ZMod m)) := by
    have h_pigeonhole : ∃ i j : ℕ, i < j ∧ ((Nat.fib i : ZMod m), (Nat.fib (i + 1) : ZMod m)) = ((Nat.fib j : ZMod m), (Nat.fib (j + 1) : ZMod m)) := by
      by_contra! h;
      have h_finite : Set.Finite (Set.range (fun n : ℕ => ((Nat.fib n : ZMod m), (Nat.fib (n + 1) : ZMod m)))) := by
        cases m <;> [ aesop; exact Set.toFinite _ ];
      exact h_finite.not_infinite <| Set.infinite_range_of_injective fun i j hij => le_antisymm ( le_of_not_gt fun hi => h _ _ hi hij.symm ) ( le_of_not_gt fun hj => h _ _ hj hij );
    aesop;
  induction' i with i ih generalizing j;
  · exact ⟨ j, hij, by simpa [ ← ZMod.natCast_eq_zero_iff ] using h_pair.1.symm ⟩;
  · specialize ih ( j - 1 ) ( Nat.lt_pred_iff.mpr hij ) ; rcases j <;> simp_all +decide [ Nat.fib_add_two ] ;
    grind
