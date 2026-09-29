-- Prove2me | solution 1 for JacSign.WZ_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:05:52.733528+00:00
-- url     : https://prove2.me/submissions/84810b19-fc95-45c8-a1aa-3d1e7b5cf5ed

-- Sol generated from Tropical/JacobiSignedMultiplicative.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedMultiplicative
import Definitions.Def_Tropical_JacobiSignedWeilFloorBound
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore

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







theorem jchar_prime (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    jchar p x = quadraticChar (ZMod p) x := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  unfold jchar
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
  congr 1
  push_cast
  simp [ZMod.natCast_val]




/-! ### The geometric statistic for a composite modulus -/








open JacSign in
theorem solution(p : ℕ) [Fact p.Prime] : WZ p = W p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [WZ, W]
  exact Finset.sum_congr rfl fun x _ => jchar_prime p _
