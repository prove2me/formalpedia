-- Prove2me | Definitions.Def_Applications_SiegelWeilE8ThetaContrarian
-- name    : Applications_SiegelWeilE8ThetaContrarian
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:46.703823+00:00
-- url     : https://prove2.me/theorems/d3d9522b-43b4-4339-bfdc-6199b9b7c0ab
-- title:
--   Aether Catalog definitions — Applications_SiegelWeilE8ThetaContrarian
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.SiegelWeilE8ThetaContrarian`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/SiegelWeilE8ThetaContrarian.lean by skeleton subtraction
import Mathlib

/-!
# Contrarian conjectures around the `E₈` / Siegel–Weil theta series

The companion file `SiegelWeilE8Theta.lean` establishes that the `E₈` vector
counts `rE8 n = 240·σ₃(n)` form the coefficient system of the weight-`4` Hecke
eigenform `E₄` (prime-power geometric form, Hecke three-term recurrence,
multiplicativity, and the global Hecke convolution identity).

Following the *contrarian* mandate, this file stress-tests bold conjectures about
that arithmetic system.  We both **prove** several nontrivial structural facts
and **disprove** two natural-looking but false strengthenings.

## Proved

* `sigma3_mod_six` — the congruence `σ₃(n) ≡ σ₁(n) (mod 6)`, a hidden linear
  relation between the weight-`4` and weight-`2` divisor systems, coming from
  `d³ ≡ d (mod 6)`.
* `sigma3_ge_cube` / `sigma3_ge` — the lower bounds `n³ ≤ σ₃(n)` and
  `n³ + 1 ≤ σ₃(n)` for `n ≥ 2`.
* `sigma3_eq_lower_bound_iff_prime` — the lower bound `σ₃(n) = n³ + 1` is attained
  **exactly** at the primes: a characterization of primality via the `E₄`
  Fourier coefficients.
* `rE8_ge_cube` — the E₈ vector count grows at least like `240·n³`.

## Disproved (contrarian counterexamples)

* `rE8_not_multiplicative` — the E₈ count `rE8` is *not* multiplicative; the
  correct coprime law necessarily carries the normalizing factor `240`.
* `hecke_recurrence_composite_fails` — the Hecke three-term recurrence genuinely
  **requires** primality of the base; it fails at `p = 6`.

See `FUTURE_DIRECTIONS.md` for the flagship open target `E₄² = E₈`
(`σ₇(n) = σ₃(n) + 120·∑ σ₃(m)σ₃(n−m)`), verified numerically here.
-/

namespace SiegelWeilE8Contrarian

open ArithmeticFunction Finset

/-- The `E₈` representation number: `rE8 n = 240·σ₃(n)` counts the vectors of
squared length `2n` in the `E₈` lattice. -/
def rE8 (n : ℕ) : ℕ := 240 * (sigma 3) n

/-! ### A hidden congruence between σ₃ and σ₁ -/



/-! ### Lower bounds and the prime characterization -/





/-! ### Contrarian disproofs -/



/-! ### Low-order corroboration -/


end SiegelWeilE8Contrarian


