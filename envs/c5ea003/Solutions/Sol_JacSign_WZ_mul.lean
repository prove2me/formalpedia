-- Prove2me | solution 1 for JacSign.WZ_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:05:52.156974+00:00
-- url     : https://prove2.me/submissions/c38309ae-550d-488b-aefc-40f203a5d508

-- Sol generated from Tropical/JacobiSignedMultiplicative.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedMultiplicative
import Definitions.Def_Tropical_JacobiSignedWeilFloorBound

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




/-- Reducing the modulus: the Jacobi symbol only sees the residue class. -/
theorem jchar_cast {N k : ℕ} [NeZero N] [NeZero k] (x : ZMod N) (hd : k ∣ N) :
    jacobiSym (x.val : ℤ) k = jchar k (ZMod.castHom hd (ZMod k) x) := by
  apply jacobiSym.mod_left'
  have h : (((x.val : ℤ)) : ZMod k) = ((((ZMod.castHom hd (ZMod k) x).val : ℤ)) : ZMod k) := by
    push_cast
    simp [ZMod.natCast_val, ZMod.castHom_apply]
  exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp h







/-! ### The geometric statistic for a composite modulus -/








open JacSign in
theorem solution(m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) :
    WZ (m * n) = WZ m * WZ n := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  set f : ZMod (m * n) →+* ZMod m := ZMod.castHom (dvd_mul_right m n) (ZMod m) with hf
  set g : ZMod (m * n) →+* ZMod n := ZMod.castHom (dvd_mul_left n m) (ZMod n) with hg
  have hsplit : ∀ x : ZMod (m * n), jchar (m * n) (x * (1 - x ^ 2))
      = jchar m (f x * (1 - (f x) ^ 2)) * jchar n (g x * (1 - (g x) ^ 2)) := by
    intro x
    show jacobiSym _ (m * n) = _
    rw [jacobiSym.mul_right]
    congr 1
    · rw [jchar_cast (k := m) (x * (1 - x ^ 2)) (dvd_mul_right m n)]
      congr 2
      simp [hf, map_mul, map_sub, map_pow]
    · rw [jchar_cast (k := n) (x * (1 - x ^ 2)) (dvd_mul_left n m)]
      congr 2
      simp [hg, map_mul, map_sub, map_pow]
  have hprod : WZ (m * n)
      = ∑ z : ZMod m × ZMod n, jchar m (z.1 * (1 - z.1 ^ 2)) * jchar n (z.2 * (1 - z.2 ^ 2)) := by
    rw [WZ, Finset.sum_congr rfl fun x _ => hsplit x]
    refine Fintype.sum_equiv (ZMod.chineseRemainder h).toEquiv _ _ fun x => ?_
    have h1 : ((ZMod.chineseRemainder h).toEquiv x).1 = f x := by
      simp [hf, ZMod.chineseRemainder]
    have h2 : ((ZMod.chineseRemainder h).toEquiv x).2 = g x := by
      simp [hg, ZMod.chineseRemainder]
    rw [h1, h2]
  rw [hprod, WZ, WZ, Finset.sum_mul_sum]
  exact Fintype.sum_prod_type _
