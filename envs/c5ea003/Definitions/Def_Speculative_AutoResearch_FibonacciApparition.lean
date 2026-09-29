-- Prove2me | Definitions.Def_Speculative_AutoResearch_FibonacciApparition
-- name    : Speculative_AutoResearch_FibonacciApparition
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:28:57.322144+00:00
-- url     : https://prove2.me/theorems/fe4ef85b-f1c4-46bb-97f6-c02d93709e4e
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_FibonacciApparition
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.FibonacciApparition`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/FibonacciApparition.lean by skeleton subtraction
import Mathlib

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

namespace FibonacciApparition

/-! ## §1. Periodicity of the Fibonacci pair-sequence modulo `m` -/

/-- The pair `(F n, F (n+1))` reduced modulo `m`. The Fibonacci recurrence makes this a
deterministic dynamical system on the finite set `ZMod m × ZMod m`. -/
def fibPair (m n : ℕ) : ZMod m × ZMod m := ((Nat.fib n : ZMod m), (Nat.fib (n + 1) : ZMod m))

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

open Classical in
/-- The **Fibonacci entry point** of `m`: the least `k > 0` with `m ∣ F k`
(`0` if none exists; by `exists_pos_dvd_fib` that fallback never triggers for `m > 0`). -/
noncomputable def fibEntry (m : ℕ) : ℕ :=
  if h : ∃ k, 0 < k ∧ m ∣ Nat.fib k then Nat.find h else 0

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



end FibonacciApparition


