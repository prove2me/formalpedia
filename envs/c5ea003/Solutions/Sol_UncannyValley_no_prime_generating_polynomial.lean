-- Prove2me | solution 1 for UncannyValley.no_prime_generating_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:49:53.060103+00:00
-- url     : https://prove2.me/submissions/9296a222-faef-4c2b-a296-269b81777749

-- Sol generated from Applications/UncannyValley/PrimeGeneratingPolynomials.lean
import Mathlib
import Definitions.Def_Applications_UncannyValley_PrimeGeneratingPolynomials

/-!
# The Uncanny Valley of Prime-Generating Formulas

A recurring illusion in number theory is the *prime-generating polynomial*: a
simple algebraic expression that produces a long, unbroken run of primes and
therefore *looks* like a formula for the primes.  The most famous example is
Euler's polynomial `n² + n + 41`, which is prime for every one of the forty
inputs `n = 0, 1, …, 39`.  A formula this accurate is squarely in the *uncanny
valley*: it is almost, but not quite, a genuine prime formula.

This file explains *why* every such formula must eventually fail.  The central
result is a clean structural obstruction:

* `UncannyValley.no_prime_generating_polynomial` — **no nonconstant integer
  polynomial takes a prime value at every integer input.**

The proof turns on the divisibility identity `f(a) ∣ f(a + k·f(a))`, isolated as
`UncannyValley.eval_dvd_eval_shift`.  If `f(a) = p` is prime, then `p` divides
`f(a + k·p)` for *every* `k`; since each of those values is itself prime, they
are all forced into the two-element set `{p, -p}`.  An infinite family of inputs
mapping into a finite set of values would make `f` constant, a contradiction.

We then return to the motivating example and exhibit both faces of the uncanny
valley for Euler's polynomial:

* `UncannyValley.euler_prime_run` — it is prime for all `n = 0, …, 39`;
* `UncannyValley.euler_not_prime_at_40` — it fails at the very next input,
  where `40² + 40 + 41 = 41²`;
* `UncannyValley.euler_polynomial_not_prime_generating` — the general theorem,
  specialised to Euler's polynomial, guarantees a failure must exist.
-/

open UncannyValley

open Polynomial

/-- **The divisibility engine.**  For an integer polynomial `f` and any integers
`a, k`, the value `f(a)` divides `f(a + k · f(a))`.  This is the arithmetic
progression that dooms every prime-generating formula: starting from a value
`f(a)`, we can reach infinitely many inputs on which `f` is divisible by it. -/
lemma eval_dvd_eval_shift (f : ℤ[X]) (a k : ℤ) :
    f.eval a ∣ f.eval (a + k * f.eval a) := by
  have := Polynomial.sub_dvd_eval_sub ( a + k * eval a f ) a f; simp_all +decide ;
  simpa using dvd_of_mul_left_dvd this

/-- A prime dividing a prime, over `ℤ`, forces equality up to sign. -/
lemma prime_dvd_prime_eq (p q : ℤ) (hp : Prime p) (hq : Prime q) (h : p ∣ q) :
    q = p ∨ q = -p := by
  obtain ⟨ k, hk ⟩ := h;
  simp_all +decide [ Int.prime_iff_natAbs_prime, Int.natAbs_mul, Nat.prime_mul_iff ];
  rw [ Int.natAbs_eq_iff ] at hq ; aesop


/-
**Strengthening — the valley has infinite width.**  A nonconstant integer
polynomial is not merely doomed to fail somewhere: it takes a non-prime value at
*infinitely many* integer inputs.  No matter how the formula is tuned, the set of
inputs on which the prime illusion breaks is infinite.
-/

/-! ### Euler's polynomial `n² + n + 41` — a tour of the uncanny valley -/








open UncannyValley in
theorem solution(f : ℤ[X])
    (hnonconst : ∀ c : ℤ, f ≠ C c)
    (hprime : ∀ n : ℤ, Prime (f.eval n)) : False := by
  obtain ⟨a, ha⟩ : ∃ a : ℤ, f.eval a ≠ 0 ∧ f.eval a ≠ 1 ∧ f.eval a ≠ -1 := by
    simp_all +decide [ Int.prime_iff_natAbs_prime ];
    exact ⟨ 0, by specialize hprime 0; aesop_cat, by specialize hprime 0; aesop_cat, by specialize hprime 0; aesop_cat ⟩;
  -- Consider the sequence $a + k \cdot f(a)$ for $k = 0, 1, 2, \ldots$
  have h_seq : ∀ k : ℤ, f.eval (a + k * f.eval a) = f.eval a ∨ f.eval (a + k * f.eval a) = -f.eval a := by
    intro k;
    exact prime_dvd_prime_eq _ _ ( hprime _ ) ( hprime _ ) ( eval_dvd_eval_shift _ _ _ );
  -- Since $f$ is nonconstant, the set $\{a + k \cdot f(a) \mid k \in \mathbb{Z}\}$ is infinite.
  have h_infinite : Set.Infinite {x : ℤ | f.eval x = f.eval a ∨ f.eval x = -f.eval a} := by
    exact Set.infinite_of_injective_forall_mem ( fun k => by aesop ) h_seq;
  -- Since $f$ is nonconstant, the polynomial $f - C(f(a))$ or $f + C(f(a))$ must be the zero polynomial.
  have h_zero_poly : f - Polynomial.C (f.eval a) = 0 ∨ f + Polynomial.C (f.eval a) = 0 := by
    exact Classical.or_iff_not_imp_left.2 fun h => Classical.not_not.1 fun h' => h_infinite <| Set.Finite.subset ( f - C ( eval a f ) |> Polynomial.roots |> Multiset.toFinset |> Finset.finite_toSet |> Set.Finite.union <| f + C ( eval a f ) |> Polynomial.roots |> Multiset.toFinset |> Finset.finite_toSet ) fun x hx => by simp_all +decide [ sub_eq_iff_eq_add, add_eq_zero_iff_eq_neg ] ;
  cases' h_zero_poly with h h <;> [ exact hnonconst ( f.eval a ) ( sub_eq_zero.mp h ) ; exact hnonconst ( -f.eval a ) ( by simpa using eq_neg_of_add_eq_zero_left h ) ]
