-- Prove2me | Theorems.Thm_SiegelWeilE8Contrarian_sigma3_eq_lower_bound_iff_prime
-- name    : SiegelWeilE8Contrarian.sigma3_eq_lower_bound_iff_prime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:02:35.491346+00:00
-- url     : https://prove2.me/theorems/8df46470-63c7-46ba-96b1-07625aae67ab
-- title:
--   Bold true.
-- statement:
--   **Bold true.**  The lower bound `σ₃(n) = n³ + 1` is attained precisely at the
--   primes.  This is a characterization of primality through the `E₄` Fourier
--   coefficients.
--
--   ```lean
--   theorem SiegelWeilE8Contrarian.sigma3_eq_lower_bound_iff_prime(n : ℕ) (hn : 2 ≤ n) :
--       (sigma 3) n = n ^ 3 + 1 ↔ n.Prime := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/PosetTheory/SiegelWeilE8ThetaContrarian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/PosetTheory/SiegelWeilE8ThetaContrarian.lean#L93

-- Thm stub generated from Applications/SiegelWeilE8ThetaContrarian.lean
import Mathlib
import Definitions.Def_Applications_SiegelWeilE8ThetaContrarian

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

open SiegelWeilE8Contrarian

open ArithmeticFunction Finset


/-! ### A hidden congruence between σ₃ and σ₁ -/



/-! ### Lower bounds and the prime characterization -/

theorem SiegelWeilE8Contrarian.sigma3_eq_lower_bound_iff_prime(n : ℕ) (hn : 2 ≤ n) :
    (sigma 3) n = n ^ 3 + 1 ↔ n.Prime := by sorry
