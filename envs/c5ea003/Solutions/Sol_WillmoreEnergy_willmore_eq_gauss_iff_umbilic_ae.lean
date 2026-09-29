-- Prove2me | solution 1 for WillmoreEnergy.willmore_eq_gauss_iff_umbilic_ae
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:38:57.579926+00:00
-- url     : https://prove2.me/submissions/bfa273d5-326f-4705-ab49-a8405e08d1dc

-- Sol generated from Geometry/WillmoreEnergy.lean
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
/-- **The pointwise square identity** `H² - K = ((k₁-k₂)/2)²`. -/
theorem willmoreDensity_sub_gaussCurv (x : X) :
    willmoreDensity k1 k2 x - gaussCurv k1 k2 x = umbilicDefect k1 k2 x := by
  unfold willmoreDensity gaussCurv umbilicDefect; ring


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

/-! ## Part 5: Genus-monotonicity of the elementary obstruction

The elementary Gauss–Bonnet floor `b(g) = 4π(1-g)` is the best lower bound the
square-identity argument can produce.  For genus `0` it is the sharp `4π`; for
`g ≥ 1` it is `≤ 0` and hence vacuous.  We make precise that the method loses
exactly `2π` of detectable energy per unit genus. -/


-- !-- 4π > 0 and (1 - g) ≤ 0 for g ≥ 1, so the product is ≤ 0. -- !--

-- !-- b(g+1) - b(g) = 4π·((1-(g+1)) - (1-g)) = -4π by `ring`. -- !--

-- !-- Since 4π > 0, multiplication by it is strictly monotone and (1 - ·) is strictly antitone. -- !--


open WillmoreEnergy in
theorem solution    (hW : Integrable (willmoreDensity k1 k2) μ)
    (hK : Integrable (gaussCurv k1 k2) μ) :
    willmoreEnergy μ k1 k2 = totalGauss μ k1 k2 ↔ k1 =ᵐ[μ] k2 := by
  constructor <;> intro h
  · have h_pointwise : ∀ x, willmoreDensity k1 k2 x - gaussCurv k1 k2 x
        = umbilicDefect k1 k2 x := willmoreDensity_sub_gaussCurv k1 k2
    have h_zero_ae : ∫ x, umbilicDefect k1 k2 x ∂μ = 0 → umbilicDefect k1 k2 =ᵐ[μ] 0 := by
      intro h_zero_ae
      have h_integrable : Integrable (umbilicDefect k1 k2) μ := by
        convert hW.sub hK using 1; ext x; aesop
      rw [MeasureTheory.integral_eq_zero_iff_of_nonneg_ae] at h_zero_ae
      · exact h_zero_ae
      · exact Filter.Eventually.of_forall fun x => sq_nonneg _
      · exact h_integrable
    simp_all +decide [willmoreEnergy, totalGauss]
    filter_upwards [h_zero_ae (by rw [← funext h_pointwise,
      MeasureTheory.integral_sub hW hK, h, sub_self])] with x hx using by
        norm_num [umbilicDefect] at hx; nlinarith
  · refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [h] with x hx using by
      unfold willmoreDensity gaussCurv; simp +decide [hx]; ring
