-- Prove2me | Theorems.Thm_Logic_QRDial_sum_pattern_single
-- name    : Logic.QRDial.sum_pattern_single
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:34:40.16055+00:00
-- url     : https://prove2.me/theorems/ef98f237-0192-4096-9933-59122ccb48e0
-- title:
--   A centred per-coordinate statistic has vanishing total over all patterns.
-- statement:
--   A centred per-coordinate statistic has vanishing total over all patterns.
--
--   ```lean
--   theorem Logic.QRDial.sum_pattern_single{σ : Type*} [Fintype σ] (a : σ → ℝ) (ha : ∑ s, a s = 0) :
--       ∀ k : ℕ, ∑ w : Fin k → σ, (∑ i, a (w i)) = 0
--     := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/QRDialOrthogonality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/QRDialOrthogonality.lean#L147

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






/-! ## The character model: `k` primes, independent uniform sign pairs -/

theorem Logic.QRDial.sum_pattern_single{σ : Type*} [Fintype σ] (a : σ → ℝ) (ha : ∑ s, a s = 0) :
    ∀ k : ℕ, ∑ w : Fin k → σ, (∑ i, a (w i)) = 0
  := by sorry
