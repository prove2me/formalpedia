-- Prove2me | solution 1 for BerggrenSpectral.berg_one_pow_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:53:39.850108+00:00
-- url     : https://prove2.me/submissions/9df28d1b-14a2-4421-ab1f-72052aeb8149

-- Sol generated from Cryptography/BerggrenSpectral/UnipotentResonance.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenSpectral_Generators
import Definitions.Def_Cryptography_BerggrenSpectral_UnipotentResonance
import Theorems.Thm_BerggrenSpectral_redMat_apply
import Theorems.Thm_BerggrenSpectral_redMat_pow

/-!
# Unipotent Berggren Resonance mod `N`, and a Factoring Barrier

The generators `M₁` and `M₃` are unipotent (`berg_charpoly_one`, `berg_charpoly_three`), so
their powers grow **polynomially** rather than exponentially.  We compute the powers in closed
form,

```
M₁ ^ k = !![1, -2k, 2k; 2k, 1 - 2k², 2k²; 2k, -2k², 1 + 2k²]
M₃ ^ k = !![1 - 2k², 2k, 2k²; -2k, 1, 2k; -2k², 2k, 1 + 2k²]
```

and deduce the two main results.

* **Exact modular resonance** (`berg_one_pow_eq_one_iff`, `berg_one_orderOf`,
  `berg_three_pow_eq_one_iff`): for every odd modulus `m`, `M₁ ^ k ≡ 1 (mod m)` **iff**
  `m ∣ k`.  Hence the multiplicative order of `M₁` mod `m` is exactly `m`: the "resonant
  frequency" of a unipotent branch is the modulus itself, never a proper divisor of it.

* **Factoring barrier** (`berg_one_gcd_barrier`, `berg_one_no_advantage`): consequently the
  unipotent branch carries **no factoring information**.  Any gcd obtained from a nonzero
  entry of `M₁ ^ k - 1` and an odd modulus `N` already divides `gcd (k², N)`, so every prime
  it reveals is a prime the exponent `k` already contains.  A Pollard-style resonance search
  along the unipotent branches of the Berggren tree is provably useless; all the arithmetic
  content must come from the hyperbolic branch `M₂` (see `HyperbolicResonance.lean`).
-/

open BerggrenSpectral

open Matrix




/-! ## Closed forms for the unipotent powers -/

/-- Closed form for the powers of the first Berggren generator. -/
theorem berg_one_pow (k : ℕ) :
    M₁ ^ k = !![1, -2 * (k : ℤ), 2 * (k : ℤ);
                2 * (k : ℤ), 1 - 2 * (k : ℤ) ^ 2, 2 * (k : ℤ) ^ 2;
                2 * (k : ℤ), -2 * (k : ℤ) ^ 2, 1 + 2 * (k : ℤ) ^ 2] := by
  induction k with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M₁, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring


/-! ## Exact resonance modulo an odd number -/






/-! ## The factoring barrier -/






open BerggrenSpectral in
theorem solution(m k : ℕ) (hm : Odd m) :
    (redMat m M₁) ^ k = 1 ↔ m ∣ k := by
  constructor
  · intro h
    have h' : redMat m (M₁ ^ k) = 1 := by rw [redMat_pow]; exact h
    have hentry := congrFun (congrFun h' 0) 1
    rw [redMat_apply, berg_one_pow] at hentry
    have h2 : ((-2 * (k : ℤ) : ℤ) : ZMod m) = 0 := by simpa [Matrix.one_apply] using hentry
    have hd : (m : ℤ) ∣ (-2 * (k : ℤ)) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp h2
    have hd2 : (m : ℤ) ∣ 2 * (k : ℤ) := (dvd_neg).mp (by simpa [neg_mul] using hd)
    have hnat : m ∣ 2 * k := by exact_mod_cast hd2
    exact (Nat.coprime_two_right.mpr hm).dvd_of_dvd_mul_left hnat
  · rintro ⟨t, rfl⟩
    rw [← redMat_pow, berg_one_pow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [redMat]
