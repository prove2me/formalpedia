-- Prove2me | Definitions.Def_Shared_MoonshineTauHecke
-- name    : Shared_MoonshineTauHecke
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:05:07.771855+00:00
-- url     : https://prove2.me/theorems/73a87756-cc24-449a-a747-bfbb438d888b
-- title:
--   Aether Catalog definitions — Shared_MoonshineTauHecke
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.MoonshineTauHecke`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/MoonshineTauHecke.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_MoonshineJExpansion

/-!
# Integrality of the `j`-quotient, and verified Hecke/Ramanujan data for `τ`

Second research cycle on top of `Shared.MoonshineJExpansion`.  That file
computed, inside the kernel, the head of the `q`-expansion of `j = E₄³/Δ` and
the first eight Ramanujan tau values.  Here we extract the structure behind
those computations.

* **Integrality.** `MoonshineTauHecke.exists_unique_jQuot`: the eta product
  `deltaPart m = ∏_{k≤m}(1-q^k)^24` is a *unit* of `ℤ⟦X⟧`, so the equation
  `deltaPart m · f = E₄³` has a unique solution `f = jQuot m` **over `ℤ`**.  No
  denominators appear: the coefficients of `q·j` are integers by pure formal
  algebra, and `MoonshineTauHecke.coeff_jQuot_head` identifies the first eight
  of them with the verified table.
* **Stability.** `MoonshineTauHecke.jQuot_stable`: the solution does not depend
  on the truncation `m` of the eta product below degree `N` once `m ≥ N - 1`, so
  "the" `q`-expansion of `j` is well defined coefficientwise without any
  analytic input.
* **Hecke relations.** `MoonshineTauHecke.tau_hecke_mul`,
  `tau_hecke_prime_square`, `tau_hecke_eight`: the multiplicativity
  `τ(2)τ(3) = τ(6)` and the recursions `τ(4) = τ(2)² - 2¹¹`,
  `τ(8) = τ(2)τ(4) - 2¹¹τ(2)` hold for the coefficients *produced by the eta
  product*, i.e. they are verified consequences of the computation rather than
  quoted facts.
* **Ramanujan's congruence.** `MoonshineTauHecke.tau_ramanujan_congruence`:
  `τ(n) ≡ σ₁₁(n) (mod 691)` for every `n ≤ 8`, again on the computed values.
* **Lehmer's question.** `MoonshineTauHecke.tau_ne_zero_below_nine`: the computed
  `τ(n)` are non-zero for `n ≤ 8` — the first verified window of Lehmer's open
  non-vanishing conjecture.

Every statement below is about `coeff n (deltaPart m)` or about the honest
power series `E4`, so nothing is asserted on the strength of tabulated data.
-/

namespace MoonshineTauHecke

open Finset PowerSeries MoonshineJ

/-! ## 1. The integral quotient `E₄³ / (Δ/q)` -/

/-- The unique power series `f` over `ℤ` with `deltaPart m · f = E₄³`. -/
noncomputable def jQuot (m : ℕ) : PowerSeries ℤ := Ring.inverse (deltaPart m) * E4 ^ 3






/-! ## 2. Hecke relations on the computed tau values

`coeff n (deltaPart m) = τ(n+1)`, so the following are the classical relations
`τ(2)τ(3) = τ(6)`, `τ(4) = τ(2)² - 2¹¹` and `τ(8) = τ(2)τ(4) - 2¹¹τ(2)`. -/




/-! ## 3. Ramanujan's congruence and Lehmer's question -/





end MoonshineTauHecke


