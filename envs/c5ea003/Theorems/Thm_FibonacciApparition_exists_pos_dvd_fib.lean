-- Prove2me | Theorems.Thm_FibonacciApparition_exists_pos_dvd_fib
-- name    : FibonacciApparition.exists_pos_dvd_fib
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:42:55.293239+00:00
-- url     : https://prove2.me/theorems/e023ab0c-7d98-43fa-aace-3c5df7b912c0
-- title:
--   Exists pos dvd fib
-- statement:
--   Formal statement of `FibonacciApparition.exists_pos_dvd_fib` from the Aether Catalog (Speculative). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem FibonacciApparition.exists_pos_dvd_fib(m : ℕ) (hm : 0 < m) : ∃ k, 0 < k ∧ m ∣ Nat.fib k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/FibonacciApparition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/FibonacciApparition.lean#L70

-- Thm stub generated from Speculative/AutoResearch/FibonacciApparition.lean
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

theorem FibonacciApparition.exists_pos_dvd_fib(m : ℕ) (hm : 0 < m) : ∃ k, 0 < k ∧ m ∣ Nat.fib k := by sorry
