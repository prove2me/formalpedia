-- Prove2me | solution 1 for FibonacciApparition.exists_pos_dvd_fib
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:40:38.088299+00:00
-- url     : https://prove2.me/submissions/6f8239b4-4e87-4695-a0e6-d0f79ec66753

-- Sol generated from Speculative/AutoResearch/FibonacciApparition.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_FibonacciApparition

/-! # The Rank of Apparition and Primitive Prime Divisors of Fibonacci Numbers

Domain: Tropical / Number Theory (cross-domain bridge to the Carmichael catalog targets).

This file develops, from scratch and `sorry`-free, the theory of the **Fibonacci entry
point** (a.k.a. the *rank of apparition*) `fibEntry m`: the least `k > 0` with `m ∣ F k`.

The key structural results are:

* `exists_pos_dvd_fib`  — every modulus `m > 0` divides some positive Fibonacci number
  (well-definedness of the rank of apparition, proved via the periodicity of the
  Fibonacci pair-sequence modulo `m`);
* `fib_dvd_iff_fibEntry_dvd` — the **law of apparition**: `m ∣ F k ↔ fibEntry m ∣ k`;
* `prime_primitive_divisor_iff` — a prime `p` is a **primitive prime divisor** of `F n`
  iff `fibEntry p = n`.

These results are the conceptual core underlying the catalog's Carmichael primitive-divisor
theorems (`fib_primitive_divisor`, `fib_carmichael`): the law of apparition is exactly the
mechanism that turns a "coprime part" computation into a primitive-divisor statement.

The whole development rests only on `Nat.fib_gcd` and `Nat.fib_dvd` from Mathlib.
-/

open FibonacciApparition

/-! ## §1. Periodicity of the Fibonacci pair-sequence modulo `m` -/


/-
!-- The backward step: the recurrence `F(n+2) = F(n) + F(n+1)` is invertible, so equal
successor-pairs force equal predecessor-pairs (subtraction in `ZMod m`). -- !--

The Fibonacci pair-map is *backward* deterministic: if the pairs at `a+1` and `b+1`
agree mod `m`, then so do the pairs at `a` and `b`.
-/
-- !-- The recurrence F(n+2)=F(n)+F(n+1) is invertible over ZMod m, so equal successor-pairs force equal predecessor-pairs via subtraction. -- !--

/-
!-- Descent: iterate `fibPair_back` `i` times to pull any coincidence back to time `0`. -- !--

Descent to the origin: a coincidence `fibPair m i = fibPair m j` with `i ≤ j` forces
`fibPair m 0 = fibPair m (j - i)`.
-/
-- !-- Iterate the backward step i times to pull any coincidence of pairs back to time 0. -- !--

/-
!-- Pigeonhole on the finite type `ZMod m × ZMod m` gives a coincidence; descent sends
it to a zero `F(j-i) ≡ 0`, i.e. `m ∣ F (j-i)`. -- !--

**Well-definedness of the rank of apparition.** Every `m > 0` divides some positive
Fibonacci number.
-/
-- !-- Pigeonhole on the finite set of Fibonacci pairs mod m yields a coincidence; descent sends it to F(j-i) ≡ 0, i.e. m ∣ F(j-i). -- !--

/-! ## §2. The Fibonacci entry point (rank of apparition) -/


/-
For `m > 0` the entry point is positive.
-/

/-
`m` divides the Fibonacci number at its own entry point.
-/

/-
Minimality: the entry point is `≤` any positive `k` with `m ∣ F k`.
-/

/-
Below the entry point, `m` divides no positive Fibonacci number.
-/

/-! ## §3. The law of apparition -/

/-
!-- `m ∣ F k` and `m ∣ F e` give `m ∣ gcd (F k) (F e) = F (gcd k e)` (`Nat.fib_gcd`);
minimality of `e` forces `gcd k e = e`, i.e. `e ∣ k`. Conversely `e ∣ k ⇒ F e ∣ F k`. -- !--

**Law of apparition.** A modulus `m > 0` divides `F k` exactly when its entry point
divides `k`. This is the divisibility backbone of the entire Fibonacci/Lucas primitive
divisor theory.
-/
-- !-- From m ∣ F k and m ∣ F e get m ∣ gcd(F k, F e) = F(gcd k e); minimality of e forces gcd k e = e, hence e ∣ k. Converse is fib_dvd. -- !--

/-! ## §4. Characterisation of primitive prime divisors -/

/-
!-- Forward: primitivity rules out `fibEntry p < n`, and `p ∣ F n` gives `fibEntry p ≤ n`,
so `fibEntry p = n`. Backward: `fibEntry_dvd_fib` and `fibEntry_min` give both halves. -- !--

**Primitive prime divisor characterisation.** A prime `p` is a primitive prime divisor
of `F n` (it divides `F n` but no earlier positive Fibonacci number) precisely when the
rank of apparition of `p` equals `n`. This recasts Carmichael's theorem as a statement
about the entry-point function.
-/
-- !-- Primitivity forbids fibEntry p < n while p ∣ F n gives fibEntry p ≤ n, so fibEntry p = n; the converse uses fibEntry_dvd_fib and fibEntry_min. -- !--

/-! ## §5. Corollaries connecting to the catalog -/




open FibonacciApparition in
theorem solution(m : ℕ) (hm : 0 < m) : ∃ k, 0 < k ∧ m ∣ Nat.fib k := by
  -- Use the pigeonhole principle to find a repeat in the sequence of pairs.
  have h_pigeonhole : ∃ i j, i < j ∧ (Nat.fib i ≡ Nat.fib j [MOD m]) ∧ (Nat.fib (i + 1) ≡ Nat.fib (j + 1) [MOD m]) := by
    have h_finite : Set.Finite ((fun n => (Nat.fib n % m, Nat.fib (n + 1) % m)) '' Set.univ) := by
      exact Set.finite_iff_bddAbove.mpr ⟨ ( m - 1, m - 1 ), by rintro x ⟨ n, -, rfl ⟩ ; exact ⟨ Nat.le_sub_one_of_lt ( Nat.mod_lt _ hm ), Nat.le_sub_one_of_lt ( Nat.mod_lt _ hm ) ⟩ ⟩;
    contrapose! h_finite;
    exact Set.infinite_of_injective_forall_mem ( fun i j hij => le_antisymm ( not_lt.1 fun hi => h_finite _ _ hi ( by simp_all +decide [ Nat.ModEq ] ) ( by simp_all +decide [ Nat.ModEq ] ) ) ( not_lt.1 fun hj => h_finite _ _ hj ( by simp_all +decide [ Nat.ModEq ] ) ( by simp_all +decide [ Nat.ModEq ] ) ) ) fun n => Set.mem_image_of_mem _ ( Set.mem_univ n );
  obtain ⟨ i, j, hij, hi, hj ⟩ := h_pigeonhole;
  induction' i with i ih generalizing j;
  · exact ⟨ j, hij, Nat.dvd_of_mod_eq_zero hi.symm ⟩;
  · contrapose! ih;
    refine' ⟨ j - 1, _, _, _, ih ⟩ <;> rcases j with ( _ | _ | j ) <;> simp_all +decide [ Nat.fib_add_two, ← ZMod.natCast_eq_natCast_iff ]
