-- Prove2me | Definitions.Def_Logic_QRDialOrthogonality
-- name    : Logic_QRDialOrthogonality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:07:42.086725+00:00
-- url     : https://prove2.me/theorems/9f908a47-ba9f-4aec-b579-139f7b2a4aac
-- title:
--   Aether Catalog definitions — Logic_QRDialOrthogonality
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.QRDialOrthogonality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/QRDialOrthogonality.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_QRDialDispersionLaws
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

namespace Logic.QRDial

/-! ## Two orthogonal dials: joint affine capture -/

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Mean squared error of the joint affine recalibration `y ≈ a + b·s + c·t`. -/
noncomputable def mse2 (y s t : ι → ℝ) (a b c : ℝ) : ℝ :=
  avg (fun i => (y i - (a + b * s i + c * t i)) ^ 2)





/-! ## The character model: `k` primes, independent uniform sign pairs -/

/-- A sign pattern at one prime: `(Jac(ℓ,p) = +1, Jac(ℓ,q) = +1)`. -/
abbrev SignPair := Bool × Bool

/-- The individual-symbol contribution of one prime: how many of `Jac(ℓ,p), Jac(ℓ,q)`
equal `+1`. -/
def indivCount (u : SignPair) : ℝ := (if u.1 then 1 else 0) + (if u.2 then 1 else 0)

/-- The product-symbol contribution of one prime: `1` when `Jac(ℓ,N) = +1`, i.e. when the
two symbols agree. -/
def prodCount (u : SignPair) : ℝ := if u.1 = u.2 then 1 else 0

/-- Centred individual count (mean `1` over the four sign pairs). -/
def indivC (u : SignPair) : ℝ := indivCount u - 1

/-- Centred product indicator (mean `1/2` over the four sign pairs). -/
noncomputable def prodC (u : SignPair) : ℝ := prodCount u - 1 / 2




/-- Sign patterns across `k` primes. -/
abbrev Pattern (k : ℕ) := Fin k → SignPair

/-- Splitting off the first coordinate of a pattern. -/
def consEquiv (σ : Type*) (k : ℕ) : σ × (Fin k → σ) ≃ (Fin (k + 1) → σ) where
  toFun p := Fin.cons p.1 p.2
  invFun w := (w 0, fun i => w i.succ)
  left_inv p := by ext <;> simp
  right_inv w := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp



/-- The individual-symbol dial over `k` primes. -/
def Sindiv (k : ℕ) (w : Pattern k) : ℝ := ∑ i, indivCount (w i)

/-- The product-symbol dial over `k` primes: the number of primes modulo which `N` is a
quadratic residue. -/
def Sprod (k : ℕ) (w : Pattern k) : ℝ := ∑ i, prodCount (w i)







end Logic.QRDial


