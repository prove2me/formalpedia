-- Prove2me | Theorems.Thm_WillmoreEnergy_willmore_ge_fourPi_mul_of_disjoint_sheets
-- name    : WillmoreEnergy.willmore_ge_fourPi_mul_of_disjoint_sheets
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:06:03.751567+00:00
-- url     : https://prove2.me/theorems/4e6ea5c5-b3f1-4dd2-99e0-d0844765ce88
-- title:
--   Li–Yau-style multiplicity bound: `n` pairwise-disjoint measurable regions,
-- statement:
--   **Li–Yau-style multiplicity bound**: `n` pairwise-disjoint measurable regions,
--   each carrying at least `4π` of Gaussian curvature, force `W ≥ 4π·n`. A point of
--   multiplicity `n` of an immersion produces exactly such `n` disjoint sheets.
--
--   ```lean
--   theorem WillmoreEnergy.willmore_ge_fourPi_mul_of_disjoint_sheets(n : ℕ) (s : Fin n → Set X)
--       (hms : ∀ i, MeasurableSet (s i))
--       (hd : Pairwise (Function.onFun Disjoint s))
--       (hW : Integrable (willmoreDensity k1 k2) μ)
--       (hK : Integrable (gaussCurv k1 k2) μ)
--       (hdeg : ∀ i, 4 * π ≤ ∫ x in s i, gaussCurv k1 k2 x ∂μ) :
--       4 * π * n ≤ willmoreEnergy μ k1 k2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/WillmoreEnergy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/WillmoreEnergy.lean#L225

-- Thm stub generated from Geometry/WillmoreEnergy.lean
import Mathlib
import Definitions.Def_Geometry_WillmoreEnergy
/-
# Willmore Energy: The Elementary Lower Bounds by Genus

This file develops the *elementary* half of the Willmore story in a clean,
measure-theoretic abstraction.  Rather than committing to a smooth immersed
surface, we model the geometric data of a closed surface as a finite measure
space `(X, μ)` together with two principal-curvature functions `k₁, k₂ : X → ℝ`.
All the algebraic and integral inequalities that underlie the classical
Willmore theory are then provable with no manifold machinery whatsoever.

## The core objects

* `meanCurv   = (k₁ + k₂)/2`            (the mean curvature `H`)
* `willmoreDensity = H² = ((k₁+k₂)/2)²` (the pointwise Willmore integrand)
* `gaussCurv  = k₁·k₂`                  (the Gaussian curvature `K`)
* `umbilicDefect = ((k₁-k₂)/2)²`        (the *traceless* second fundamental form)
* `willmoreEnergy = ∫ H² dμ`            (the Willmore energy `W`)

## Main results

* `willmoreDensity_sub_gaussCurv` — the pointwise identity `H² - K = ((k₁-k₂)/2)²`.
* `willmoreDensity_eq_gaussCurv_iff` — pointwise rigidity `H² = K ↔ k₁ = k₂`.
* `willmoreEnergy_sub_gauss_eq_defect` — the integral identity `W - ∫K = ∫((k₁-k₂)/2)²`.
* `gauss_le_willmore` — the integral inequality `∫K ≤ W`.
* `willmore_eq_gauss_iff_umbilic_ae` — integral rigidity: `W = ∫K ↔ k₁ = k₂` a.e.
* `gaussBonnet_bound` — `2π·χ ≤ W` from a Gauss–Bonnet input `∫K = 2π·χ`.
* `willmore_ge_fourPi_genus_zero` — the sharp `4π` bound for genus `0`.
* `willmore_ge_fourPi_of_setGauss` — the universal `4π` bound from a Gauss-map
  degree region.
* `willmore_ge_fourPi_mul_of_disjoint_sheets` — a Li–Yau-style multiplicity bound:
  `n` disjoint `4π`-sheets force `W ≥ 4π·n`.
* `gaussBonnet_bound_vacuous_high_genus` — the elementary bound `4π(1-g) ≤ 0`
  degenerates for `g ≥ 1`.
* `elementary_bound_step` / `elementary_bound_antitone` — the elementary
  obstruction loses exactly `2π` per unit genus.

This file connects to the catalog file `DiscreteGaussBonnet.lean`
(`total_curvature_eq_genus`, `eulerChar_eq_two_sub_two_mul_genus`,
`sphere_euler_char`): the Euler characteristic / genus inputs to the
Gauss–Bonnet theorems below are exactly the discrete totals proved there.

## References

* Willmore, T.J. "Note on embedded surfaces."
* Li, P. and Yau, S.-T. "A new conformal invariant and its applications…"
* Marques, F.C. and Neves, A. "Min-max theory and the Willmore conjecture."
-/

-- !-- Lab Notebook -- !--
-- Hypothesis: The classical chain of Willmore inequalities (H²≥K pointwise,
--   hence ∫K ≤ W, hence 2πχ ≤ W via Gauss–Bonnet, hence the 4π genus-0 bound)
--   is *entirely algebraic + measure-theoretic*; no smooth manifold structure
--   is needed if the principal curvatures are taken as raw measurable functions.
-- Result: Confirmed. Every elementary inequality reduces to the single square
--   identity H² - K = ((k₁-k₂)/2)² plus nonnegativity of integrals of squares.
-- Insight: The "slack" in ∫K ≤ W is *literally* an L² norm of the traceless
--   second fundamental form, so the bound upgrades to an identity-with-remainder
--   and to an a.e.-umbilic rigidity statement for free.
-- Failure analysis: The elementary method cannot see genus ≥ 1 sharp bounds:
--   for g ≥ 1 the Gauss–Bonnet floor 4π(1-g) ≤ 0 is vacuous, which we make
--   precise. The genuine genus-1 floor 2π² needs min-max input absent here.


open MeasureTheory Real

open WillmoreEnergy

variable {X : Type*} (k1 k2 : X → ℝ)

/-! ## Part 1: Pointwise objects and the square identity -/





-- !-- The square identity H² - K = ((k₁-k₂)/2)² is a single `ring` fact: it is the polarization (a+b)² - 4ab = (a-b)² rescaled by 1/4. -- !--


-- !-- The difference H² - K equals the nonnegative defect, so K ≤ H² pointwise. -- !--


-- !-- Pointwise rigidity: the square defect ((k₁-k₂)/2)² vanishes iff k₁=k₂, so H²=K exactly at umbilic points. -- !--

/-! ## Part 2: The Willmore energy and the integral inequalities -/

variable [MeasurableSpace X] {μ : Measure X}




-- !-- Integrate the pointwise identity term by term via `integral_sub`; the defect integrability follows from that of density and curvature. -- !--


-- !-- The slack W - ∫K equals the nonnegative defect integral, hence ∫K ≤ W. -- !--

-- !-- The nonnegative defect integrand integrates to 0 iff it is a.e. 0 (`integral_eq_zero_iff_of_nonneg_ae`), i.e. k₁ = k₂ a.e. -- !--

/-! ## Part 3: Gauss–Bonnet bounds and the genus-0 sharp constant

The total Gaussian curvature is supplied by the Gauss–Bonnet theorem as
`∫K = 2π·χ`.  In the catalog this `χ` is the discrete Euler characteristic of
`DiscreteGaussBonnet.lean`; here we take the identity as a hypothesis and feed
it through the elementary inequality. -/

-- !-- Combine `gauss_le_willmore` with the Gauss–Bonnet input ∫K = 2πχ. -- !--

-- !-- A genus-0 surface has χ = 2, so the Gauss–Bonnet bound becomes 4π ≤ W. -- !--

/-! ## Part 4: The Gauss-map degree mechanism (the universal 4π bound) -/

-- !-- On any region s: ∫_s K ≤ ∫_s H² ≤ ∫ H² since H² ≥ 0; chain with the degree input ∫_s K ≥ 4π. -- !--

-- !-- Each disjoint sheet contributes ≥ 4π; finite additivity (`integral_iUnion_ae`) sums them to ≥ 4π·n over the union, and H² ≥ K ≥ 0 lifts the union integral to W. -- !--

theorem WillmoreEnergy.willmore_ge_fourPi_mul_of_disjoint_sheets(n : ℕ) (s : Fin n → Set X)
    (hms : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Function.onFun Disjoint s))
    (hW : Integrable (willmoreDensity k1 k2) μ)
    (hK : Integrable (gaussCurv k1 k2) μ)
    (hdeg : ∀ i, 4 * π ≤ ∫ x in s i, gaussCurv k1 k2 x ∂μ) :
    4 * π * n ≤ willmoreEnergy μ k1 k2 := by sorry
