-- Prove2me | Theorems.Thm_mme_certified_entropy_rational_floor
-- name    : mme_certified_entropy_rational_floor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T21:01:13.162826+00:00
-- url     : https://prove2.me/theorems/73664ca1-13c0-4e9a-bb81-a667d083eacf
-- title:
--   Rational floor and ceiling for entropy from exact arithmetic
-- statement:
--   A purely rational floor and ceiling for the entropy of a rational distribution.
--
--   Given nonnegative rational weights `p` and, for each letter, four integer exponents describing a
--   reference `2^a 3^b 5^c 7^d`, the Gibbs bounds give an enclosure of the entropy whose only
--   transcendental content is `log 2`, `log 3`, `log 5` and `log 7`. Collecting the coefficients of
--   those four logarithms into four rationals turns the enclosure into a rational expression, provided
--   one has rational enclosures of the four constants; those are supplied here, certified to within
--   `10^-24` by the auto-scaled logarithm series.
--
--   The result is that a lower (or upper) bound on an entropy follows from two purely rational
--   identities: one for the quadratic part of the Gibbs bound, one for each of the four logarithm
--   coefficients. Both identities are decidable, so an entropy floor can be certified by exact
--   arithmetic alone.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_auto_scaled_log_interval_data
import Theorems.Thm_mme_certified_entropy_bounds
import Theorems.Thm_mme_log_interval_of_auto_scaled_rational
open BigOperators MME MME.RegionRate MME.Cert Finset
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
universe u

theorem mme_certified_entropy_rational_floor :
    (∀ {W : Type u} [Fintype W] (p : W → ℚ), (∀ w, 0 ≤ p w) → ∀ (e : W → Fin 4 → ℤ)
      (R : ℚ) (A : Fin 4 → ℚ),
      ∑ w, (p w - (p w) ^ 2 / qvalQ (e w)) = R →
      (∀ j, ∑ w, p w * ((e w j : ℤ) : ℚ) = A j) →
      ((R - ∑ j, (if 0 ≤ A j then A j * logHi j else A j * logLo j) : ℚ) : ℝ) ≤
        entropy (fun w ↦ ((p w : ℚ) : ℝ))) ∧
    (∀ {W : Type u} [Fintype W] (p : W → ℚ), (∀ w, 0 ≤ p w) → ∀ (e : W → Fin 4 → ℤ)
      (S : ℚ) (A : Fin 4 → ℚ),
      ∑ w, (qvalQ (e w) - p w) = S →
      (∀ j, ∑ w, p w * ((e w j : ℤ) : ℚ) = A j) →
      entropy (fun w ↦ ((p w : ℚ) : ℝ)) ≤
        ((S - ∑ j, (if 0 ≤ A j then A j * logLo j else A j * logHi j) : ℚ) : ℝ)) ∧
    (∀ j : Fin 4, ((logLo j : ℚ) : ℝ) ≤ Real.log (primeOf j)) ∧
    ∀ j : Fin 4, Real.log (primeOf j) ≤ ((logHi j : ℚ) : ℝ) := by sorry
