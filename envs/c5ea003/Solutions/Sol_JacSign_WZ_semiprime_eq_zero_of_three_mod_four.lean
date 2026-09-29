-- Prove2me | solution 1 for JacSign.WZ_semiprime_eq_zero_of_three_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:10:24.902321+00:00
-- url     : https://prove2.me/submissions/d63169cb-8fb5-4d0a-ab0c-cf0ed602ed62

-- Sol generated from Tropical/JacobiSignedMultiplicative.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedMultiplicative
import Definitions.Def_Tropical_JacobiSignedWeilFloorBound
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore
import Theorems.Thm_JacSign_WZ_mul
import Theorems.Thm_JacSign_WZ_prime
import Theorems.Thm_JacSign_W_eq_zero_of_three_mod_four

/-!
# Multiplicativity of the Jacobi-signed circle count and the semiprime Weil floor

The Jacobi-signed circle count is defined for an arbitrary modulus `n` by weighting the
circle `x² + y² = 1` over `ZMod n` with the *Jacobi symbol* `(x / n)`.  Summing the `y`'s
away, this is the character sum

`WZ n = ∑_{x : ZMod n} (x(1-x²) / n)`.

Main results.

* `JacSign.jchar_mul` : `x ↦ (x / n)` is multiplicative on `ZMod n`.
* `JacSign.WZ_mul` : `WZ (m n) = WZ m · WZ n` for coprime moduli — the Chinese remainder
  theorem turns the circle count into a **symmetric product over the factors**.
* `JacSign.WZ_prime` : for a prime modulus the Jacobi-signed count is the Legendre
  character sum `W p` of the core file.
* `JacSign.WZ_semiprime` : `WZ (p q) = W p · W q` for distinct primes.
* `JacSign.WZ_semiprime_sq_le` : `WZ (p q) ^ 2 ≤ 16 · p q`, i.e. `|WZ N| ≤ 4 √N`:
  **the semiprime Weil floor.**  The signal available to a factoring witness is
  `O(√N)` against a search space of size `N`.
* `JacSign.WZ_semiprime_eq_zero_of_three_mod_four` : if either prime is `≡ 3 (mod 4)`
  the whole statistic vanishes.
-/

open Finset

open JacSign









/-- **The semiprime factorisation of the statistic**: `W(N) = W(p)·W(q)`. -/
theorem WZ_semiprime {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) :
    WZ (p * q) = W p * W q := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hcop : p.Coprime q := (Nat.coprime_primes (Fact.out) (Fact.out)).mpr hpq
  rw [WZ_mul p q hcop, WZ_prime, WZ_prime]


/-! ### The geometric statistic for a composite modulus -/








open JacSign in
theorem solution{p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (h : p % 4 = 3 ∨ q % 4 = 3) : WZ (p * q) = 0 := by
  rw [WZ_semiprime hpq]
  rcases h with h | h
  · rw [W_eq_zero_of_three_mod_four p h, zero_mul]
  · rw [W_eq_zero_of_three_mod_four q h, mul_zero]
