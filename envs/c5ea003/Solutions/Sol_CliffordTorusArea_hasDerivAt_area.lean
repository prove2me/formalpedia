-- Prove2me | solution 1 for CliffordTorusArea.hasDerivAt_area
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:06:45.336417+00:00
-- url     : https://prove2.me/submissions/8759d67e-e605-4a26-8ec5-9d8fbff5a127

-- Sol generated from Shared/CliffordTorusAreaRefutation.lean
import Mathlib
import Definitions.Def_Shared_CliffordTorusAreaRefutation
import Theorems.Thm_CliffordTorusArea_area_eq

/-!
# Hopf-invariant tori in `S³`: the Clifford torus maximizes, and does not minimize, area

`FourthDimensionPlayground.clifford_torus_equator` identifies the Clifford torus
`|z| = |w|` inside the unit three-sphere as the Hopf preimage of the equator of
`S²`.  A Phase-A conjecture proposed that, among embedded tori of `S³` invariant
under the diagonal circle action and separating the two coordinate circles, the
Clifford torus *uniquely minimizes area*.

This file refutes that conjecture inside the most natural test family — the
Hopf-invariant flat tori
`T r = { (z, w) : ‖z‖ = r, ‖w‖ = √(1 - r²) }`, `0 < r < 1` — and proves the
corrected statement: the Clifford torus is the unique **maximizer** of area in
this family, while the area infimum over the family is `0`, so no minimizer
exists at all.

The area is not postulated: it is computed from the first fundamental form of the
explicit parametrization `(s, t) ↦ (r e^{is}, √(1-r²) e^{it})`, whose tangent
vectors are verified to be genuine derivatives (`hasDerivAt_param_fst`,
`hasDerivAt_param_snd`), and then integrated over the fundamental square.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer):
Diagonal-circle-invariant tori separating the two coordinate circles form a
one-parameter family `T r`; the conjecture predicts the Clifford torus `r = √2/2`
to be the unique area minimizer.

Experiment (Experimenter):
The induced metric of the parametrization is `E = r²`, `F = 0`, `G = 1 - r²`,
hence `area (T r) = 4π² r √(1 - r²)`.  Numerically: `r = 0.7071 → 19.739`,
`r = 0.5 → 17.093`, `r = 0.1 → 3.929`, `r = 0.01 → 0.395`.  The value at the
Clifford parameter is the *largest*, not the smallest, and the family's areas
tend to `0`.

Analysis (Analyst):
By AM–GM, `r √(1 - r²) ≤ 1/2` with equality exactly at `r² = 1/2`, so the
Clifford torus is the unique maximizer, of area `2π²`.  The conjecture is
therefore false as stated; what is true (Marques–Neves) is minimality among
*minimal* tori, i.e. a constrained problem, and the correct unconstrained
extremal property of the Clifford torus in this symmetry class is maximality.
The failure is of type "false as stated / needs a different variational class",
not "true but hard".

Critique (Critic):
The refutation is not vacuous: every `T r` with `0 < r < 1` is a genuine embedded
torus in `S³` (`param_mem_sphere`), is invariant under the diagonal circle action
(`param_diagonal_invariant`), and separates the two coordinate circles in the
concrete sense that the first coordinate circle has `‖z‖ = 1 > r` while the
second has `‖z‖ = 0 < r` (`torus_separates_coordinate_circles`).  The degenerate
parameters `r = 0, 1` are excluded, and the area is derived rather than assumed.

Synthesis (Principal Investigator):
Within the Hopf-symmetric class, area is the single function `4π² r √(1-r²)`;
its unique interior critical point is the Clifford torus, and it is a maximum.
Any correct extremality statement for the Clifford torus must therefore be
constrained (minimal surfaces, Willmore energy) rather than a plain area
minimization.
-- !-- Lab Notes -- !--
-/

open Complex Real ComplexConjugate intervalIntegral

open CliffordTorusArea

noncomputable section







/-! ### The parametrization and its derivatives -/









/-! ### The first fundamental form -/





/-! ### Area of the Hopf-invariant tori -/






/-! ### Refutation of the minimality conjecture -/





/-! ### Criticality: what the Clifford parameter really satisfies -/






open CliffordTorusArea in
theorem solution(r : ℝ) (h0 : 0 < r) (h1 : r < 1) :
    HasDerivAt area (4 * π ^ 2 * ((1 - 2 * r ^ 2) / Real.sqrt (1 - r ^ 2))) r := by
  have hpos : 0 < 1 - r ^ 2 := by nlinarith
  have hne : (1 - r ^ 2) ≠ 0 := ne_of_gt hpos
  have hs : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.mpr hpos
  have hinner : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * r)) r := by
    simpa using ((hasDerivAt_pow 2 r).const_sub 1)
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2))
      (-((Real.sqrt (1 - r ^ 2))⁻¹ * 2⁻¹ * (2 * r))) r := by
    simpa using (Real.hasDerivAt_sqrt hne).comp r hinner
  have h := ((hasDerivAt_id r).mul hsqrt).const_mul (4 * π ^ 2)
  have hform : HasDerivAt (fun x : ℝ => 4 * π ^ 2 * (x * Real.sqrt (1 - x ^ 2)))
      (4 * π ^ 2 * ((1 - 2 * r ^ 2) / Real.sqrt (1 - r ^ 2))) r := by
    convert h using 1
    simp only [id_eq]
    field_simp
    nlinarith [Real.sq_sqrt hpos.le, hs]
  refine hform.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds h0 h1] with x hx
  exact area_eq x hx.1.le hx.2.le
