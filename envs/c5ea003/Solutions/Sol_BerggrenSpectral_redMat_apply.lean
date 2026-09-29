-- Prove2me | solution 1 for BerggrenSpectral.redMat_apply
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:52:02.54788+00:00
-- url     : https://prove2.me/submissions/d602c951-0628-4bdd-b2bc-e8015a60a59b

-- Sol generated from Cryptography/BerggrenSpectral/UnipotentResonance.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenSpectral_Generators
import Definitions.Def_Cryptography_BerggrenSpectral_UnipotentResonance

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



/-! ## Exact resonance modulo an odd number -/






/-! ## The factoring barrier -/






open BerggrenSpectral in
theorem solution(m : ℕ) (A : Matrix (Fin 3) (Fin 3) ℤ) (i j : Fin 3) :
    redMat m A i j = ((A i j : ℤ) : ZMod m) := rfl
