-- Prove2me | solution 1 for CliffordTorusArea.clifford_unique_critical_point
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:08:44.932865+00:00
-- url     : https://prove2.me/submissions/03b5e190-34e3-4cce-a628-9b55459c9cad

-- Sol generated from Shared/CliffordTorusAreaRefutation.lean
import Mathlib
import Definitions.Def_Shared_CliffordTorusAreaRefutation
import Theorems.Thm_CliffordTorusArea_hasDerivAt_area

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
    deriv area r = 0 ↔ r = Real.sqrt 2 / 2 := by
  have hpos : 0 < 1 - r ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.mpr hpos
  have hp2 : (0:ℝ) < π ^ 2 := by positivity
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [(hasDerivAt_area r h0 h1).deriv]
  constructor
  · intro h
    have h4 : (4:ℝ) * π ^ 2 ≠ 0 := by positivity
    have hnum : 1 - 2 * r ^ 2 = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' h4
      · exact (div_eq_zero_iff.mp h').resolve_right (ne_of_gt hs)
    have hr2 : r ^ 2 = (Real.sqrt 2 / 2) ^ 2 := by nlinarith
    rw [← Real.sqrt_sq h0.le, hr2, Real.sqrt_sq (by positivity)]
  · intro h
    subst h
    have : 1 - 2 * (Real.sqrt 2 / 2) ^ 2 = 0 := by nlinarith
    rw [this]
    simp
