-- Prove2me | Definitions.Def_Applications_EisensteinPowerCongruence
-- name    : Applications_EisensteinPowerCongruence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:44:43.633266+00:00
-- url     : https://prove2.me/theorems/9968e212-b521-41c0-83c3-c931aa2d47c1
-- title:
--   Aether Catalog definitions — Applications_EisensteinPowerCongruence
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.EisensteinPowerCongruence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/EisensteinPowerCongruence.lean by skeleton subtraction
import Mathlib
/-
# From the `E₄² = E₈` identity to elementary divisor-sum congruences

A *connector* result.  On the modular-forms side, the ring of level-one modular
forms is so rigid that in weight `8` there is a unique normalized form, forcing
the Eisenstein identity `E₄² = E₈`.  Comparing `q`-expansions of

  `E₄ = 1 + 240 ∑ σ₃(n) qⁿ`,   `E₈ = 1 + 480 ∑ σ₇(n) qⁿ`

yields, after dividing by `480`, the exact convolution law

  `σ₇(n) = σ₃(n) + 120 · ∑_{i=1}^{n-1} σ₃(i) σ₃(n−i)`,

and in particular the congruence `σ₇(n) ≡ σ₃(n) (mod 120)`.

This file proves the *arithmetic shadow* of that transcendental identity by purely
elementary means, and shows that the whole phenomenon is governed by a single
reusable bridge:

* `pow_pow_dvd_of_zmod` / `pow7_sub_pow3_dvd`, `pow5_sub_pow3_dvd` — the pointwise
  power-residue laws `120 ∣ d⁷ − d³` and `24 ∣ d⁵ − d³`, proved by finite
  computation in `ZMod`.
* `sigma_sub_dvd_of_pow` — **the connector**: any pointwise power congruence
  `m ∣ aʲ − aᵏ` transfers verbatim to the divisor sums,
  `m ∣ σⱼ(n) − σₖ(n)`, because a divisor sum is a sum of powers.
* `sigma7_sub_sigma3_dvd`, `sigma5_sub_sigma3_dvd` — the resulting divisor-sum
  congruences `σ₇(n) ≡ σ₃(n) (mod 120)` and `σ₅(n) ≡ σ₃(n) (mod 24)`.
* `pow7_modulus_isGreatest`, `sigma7_modulus_isGreatest` — **sharpness**: `120`
  is the *largest* modulus for which either congruence holds for all inputs
  (witnessed at `a = 2`, resp. `n = 2`).
* `pow5_modulus_isGreatest`, `sigma5_modulus_isGreatest` — the weight-`6`
  sharpness analogue: `24` is the largest modulus for `d⁵ ≡ d³` / `σ₅ ≡ σ₃`.
* `E8_normalized_congruence` — scaling by the `E₈` vector-count normalization
  `240` gives `28800 ∣ 240·σ₇(n) − 240·σ₃(n)`, the modulus against which the
  rank-`16` even unimodular genus (`E₈ ⊕ E₈` vs `D₁₆⁺`) is compared.
* `convolution_law_two`, … `convolution_law_five` — concrete instances of the
  exact convolution law confirming the arithmetic reproduces the `q`-expansion
  coefficients term by term.

Everything below is elementary and self-contained; the modular-forms input is used
only as motivation.
-/

open Finset

namespace EisensteinPowerCongruence

set_option maxRecDepth 4000

/-- The integer-valued divisor power sum `σ_k(n) = ∑_{d ∣ n} d^k`. -/
def sigmaZ (k n : ℕ) : ℤ := ∑ d ∈ n.divisors, (d : ℤ) ^ k


/-! ## Pointwise power-residue laws -/




/-! ## The connector: pointwise congruences transfer to divisor sums -/




/-! ## Sharpness of the modulus `120` -/





/-! ## Cross-domain corollary: the rank-16 even unimodular genus modulus -/


/-! ## Concrete instances of the exact convolution law (Direction 1)

The self-convolution `(σ₃ ⋆ σ₃)(n) = ∑_{i=1}^{n-1} σ₃(i) σ₃(n−i)`. -/

/-- The Dirichlet-style self-convolution of `σ₃` over the range `1 ≤ i ≤ n−1`. -/
def conv3 (n : ℕ) : ℤ := ∑ i ∈ Finset.Ico 1 n, sigmaZ 3 i * sigmaZ 3 (n - i)





end EisensteinPowerCongruence


