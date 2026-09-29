-- Prove2me | Theorems.Thm_Logic_QRDial_two_dial_capture_bound
-- name    : Logic.QRDial.two_dial_capture_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:34:49.190981+00:00
-- url     : https://prove2.me/theorems/588518e4-c80d-4863-be7b-efe82b13a532
-- title:
--   Joint capture bound for two orthogonal dials.
-- statement:
--   **Joint capture bound for two orthogonal dials.**  When `cov s t = 0` the explained
--   shares of the two dials simply add: no affine function of both can push the residual below
--   `var y − cov(y,s)²/var s − cov(y,t)²/var t`.
--
--   ```lean
--   theorem Logic.QRDial.two_dial_capture_bound(y s t : ι → ℝ) (hs : 0 < var s) (ht : 0 < var t)
--       (hst : cov s t = 0) (a b c : ℝ) :
--       var y - (cov y s) ^ 2 / var s - (cov y t) ^ 2 / var t ≤ mse2 y s t a b c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/QRDialOrthogonality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/QRDialOrthogonality.lean#L59

-- Thm stub generated from Logic/QRDialOrthogonality.lean
import Mathlib
import Definitions.Def_Logic_QRDialDispersionLaws
import Definitions.Def_Logic_QRDialOrthogonality
/-
# Exact orthogonality of the individual-symbol and product-symbol QR dials

The exp-576 robustness catch asserts that the two small-prime quadratic-residue dials are
*analytically* uncorrelated under independent characters:

* `S_indiv = #{(ℓ, side) : Jac(ℓ, p) = +1 or Jac(ℓ, q) = +1}`, the individual-symbol count;
* `S_prod  = #{ℓ : N is a QR mod ℓ} = #{ℓ : Jac(ℓ,p)·Jac(ℓ,q) = +1}`, the product-symbol
  count, which is the dial that actually controls the divisibility carrier
  (`ℓ ∣ x² − N` is possible iff `Jac(ℓ,N) = +1`).

Modelling the pair of Legendre symbols at each of `k` primes as an independent uniform
pair of signs, this file proves `Cov(S_indiv, S_prod) = 0` **exactly**, for every `k`
(`Logic.QRDial.cov_Sindiv_Sprod_eq_zero`), not merely to the measured `r = −0.01`.

The mechanism is a one-prime identity (`Logic.QRDial.char_cov_single_prime`): on the
four-point space of sign pairs the centred individual count `(+1,+1) ↦ 1`, `(±1,∓1) ↦ 0`,
`(−1,−1) ↦ −1` is *odd* under global sign flip while the centred product indicator is
*even*, so their inner product cancels in pairs.  Independence across primes then
propagates the cancellation additively; this is proved by an induction over the number of
primes with the general lemma `Logic.QRDial.sum_pattern_prod`.

The consequence for the verdict is `Logic.QRDial.two_dial_capture_bound`: because the two
dials are orthogonal, their explained-variance shares simply add, so *no* joint affine
recalibration of both dials can explain more than `r₁² + r₂²`.  With the measured
`r₁² = 0.0127` and `r₂² = 0.0781` this leaves at least `90.9%` of the log-rate variance
unexplained (`Logic.QRDial.exp576_two_dial_residual`), well outside the pre-registered
H1 bar of `30%`.
-/

open Finset

open Logic.QRDial

/-! ## Two orthogonal dials: joint affine capture -/

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem Logic.QRDial.two_dial_capture_bound(y s t : ι → ℝ) (hs : 0 < var s) (ht : 0 < var t)
    (hst : cov s t = 0) (a b c : ℝ) :
    var y - (cov y s) ^ 2 / var s - (cov y t) ^ 2 / var t ≤ mse2 y s t a b c := by sorry
