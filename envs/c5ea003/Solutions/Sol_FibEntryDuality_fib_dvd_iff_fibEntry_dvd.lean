-- Prove2me | solution 1 for FibEntryDuality.fib_dvd_iff_fibEntry_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:49:41.120819+00:00
-- url     : https://prove2.me/submissions/476e744b-e410-4fc6-a1d3-cb0ebeffeb79

-- Sol generated from Novelty/FibonacciEntryPointDuality.lean
import Mathlib
import Definitions.Def_Novelty_FibonacciEntryPointDuality

/-!
# Entry-Point Duality for the Fibonacci sequence

For a modulus `p`, the **entry point** (rank of apparition) `z(p) = fibEntry p` is the
least positive index `k` with `p ∣ F k` (and `0` if no such index exists).  This file
isolates the single biconditional from which the scattered, one-directional
entry-point lemmas of the catalog all follow:

* `fib_dvd_iff_fibEntry_dvd` — the master *duality* `p ∣ F n ↔ z(p) ∣ n`.  It turns a
  divisibility question about Fibonacci numbers into a divisibility question about a
  single arithmetic function `z`.
* `isFibPrimitiveDivisor_iff_entry` — a prime `p` is a *primitive* divisor of `F n`
  iff `z(p) = n`; primitivity collapses to one equation.
* `fib_dvd_iff` — the strong-divisibility law `F m ∣ F n ↔ m ∣ n` for `m ≥ 3`,
  recovered as the special case `p = F m` of the duality.
* `fib_primitive_divisor_verified` — a `native_decide` certificate of Carmichael's
  primitive-divisor theorem for `1 ≤ n ≤ 40`, `n ∉ {1,2,6,12}`.

The whole development is self-contained over Mathlib: the only Fibonacci-specific
inputs are `Nat.fib_gcd` and `Nat.fib_dvd`.

## Catalog synthesis

This unifies and generalizes the one-directional entry-point lemmas previously
scattered across the catalog: `CarmichaelComposite.fibEntryPt_dvd_of_fib_dvd`
(forward direction only, stated for primes), the LTE file's `fibEntryPoint`, and the
primitive-divisor predicates of `Applications.FibonacciPrimitiveDivisors`.  The new
content is that all of these are corollaries of one biconditional, which moreover
needs no primality hypothesis.

-- !-- Lab Notebook -- !--
-- !-- Hypothesis: the divisibility relation `p ∣ F n` is governed entirely by the
--     entry-point map `z`, via the principal-ideal identity `p ∣ F n ↔ z(p) ∣ n`,
--     with no primality hypothesis required. -- !--
-- !-- Result: proved the biconditional for arbitrary `p`, derived the primitive-divisor
--     characterization `z(p)=n`, the strong-divisibility law `F m ∣ F n ↔ m ∣ n`
--     (`m ≥ 3`), and a finite Carmichael certificate. -- !--
-- !-- Insight: `Nat.fib_gcd` collapses "two simultaneous apparitions" into one
--     apparition at the gcd, so minimality of `z(p)` forces `z(p) ∣ n`; the converse
--     is pure `Nat.fib_dvd`.  Everything else is divisibility algebra in ℕ. -- !--
-- !-- Failure analysis: the only care needed is the `n = 0` / "no entry point" boundary,
--     handled uniformly because `0 ∣ n ↔ n = 0` and `F 0 = 0`. -- !--
-- !-- End Lab Notebook -- !--
-/

open FibEntryDuality


/-
!-- If `p ∣ F a` and `p ∣ F b` then `p ∣ F (gcd a b)`, since `F (gcd a b) = gcd (F a) (F b)`. -- !--
-/
lemma fib_dvd_gcd {p a b : ℕ} (ha : p ∣ Nat.fib a) (hb : p ∣ Nat.fib b) :
    p ∣ Nat.fib (Nat.gcd a b) := by
  exact Nat.dvd_gcd ha hb |> fun h => dvd_trans h ( by simp +decide [ Nat.fib_gcd ] )

/-
!-- The master duality: `p ∣ F n` iff the entry point of `p` divides `n`.  Forward by
minimality of the entry point applied to `F (gcd n (z p)) = gcd (F n) (F (z p))`;
backward by `Nat.fib_dvd`.  Boundary `n = 0` is handled by `0 ∣ n ↔ n = 0`. -- !--
-/


/-
!-- Primitivity collapses to the single equation `z(p) = n`: a prime dividing `F n`
(with `n > 0`) is primitive iff its entry point is exactly `n`, both directions
via `fib_dvd_iff_fibEntry_dvd`. -- !--
-/

/-
!-- The entry point of `F m` is `m` for `m ≥ 3`: `z(F m) ∣ m` by the duality, and
`F (z) = F m` by mutual divisibility forces `z = m` since `fib` is injective on
indices `≥ 3`. -- !--
-/

/-
!-- Strong divisibility: `F m ∣ F n ↔ m ∣ n` for `m ≥ 3`, the special case `p = F m`
of the duality together with `fibEntry_fib`. -- !--
-/


/-
!-- Carmichael's primitive-divisor theorem for `1 ≤ n ≤ 40`, `n ∉ {1,2,6,12}`:
the tabulated witness is a primitive divisor in every case (`native_decide`). -- !--
-/


open FibEntryDuality in
theorem solution(p n : ℕ) :
    p ∣ Nat.fib n ↔ fibEntry p ∣ n := by
  constructor;
  · by_cases h : ∃ k, 0 < k ∧ p ∣ Nat.fib k <;> simp_all +decide [ fibEntry ];
    · intro hn
      have h_gcd : p ∣ Nat.fib (Nat.gcd n (Nat.find h)) := by
        exact fib_dvd_gcd hn ( Nat.find_spec h |>.2 );
      contrapose! h_gcd;
      exact fun h' => not_le_of_gt ( Nat.lt_of_le_of_ne ( Nat.le_of_dvd ( Nat.find_spec h |>.1 ) ( Nat.gcd_dvd_right _ _ ) ) fun con => h_gcd <| con.symm ▸ Nat.gcd_dvd_left _ _ ) ( Nat.find_min' h ⟨ Nat.gcd_pos_of_pos_right _ ( Nat.find_spec h |>.1 ), h' ⟩ );
    · cases n <;> aesop;
  · by_cases h : ∃ k, 0 < k ∧ p ∣ Nat.fib k <;> simp_all +decide [ fibEntry ];
    · exact fun hn => Nat.dvd_trans ( Nat.find_spec h |>.2 ) ( Nat.fib_dvd _ _ hn );
    · cases n <;> aesop
