-- Prove2me | solution 1 for CliffordTorusArea.area_small
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:06:44.571153+00:00
-- url     : https://prove2.me/submissions/ad0a2722-bb8d-47a3-bb9b-61ae5262326e

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
theorem solution(δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ 0 < area r ∧ area r < δ := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  refine ⟨min (1/2) (δ / (8 * π ^ 2)), lt_min (by norm_num) (by positivity),
    lt_of_le_of_lt (min_le_left _ _) (by norm_num), ?_, ?_⟩
  · set r := min (1/2) (δ / (8 * π ^ 2)) with hr
    have hr0 : 0 < r := lt_min (by norm_num) (by positivity)
    have hr1 : r ≤ 1/2 := min_le_left _ _
    have hnn : (0:ℝ) ≤ 1 - r ^ 2 := by nlinarith
    have hspos : 0 < Real.sqrt (1 - r ^ 2) :=
      Real.sqrt_pos.mpr (by nlinarith)
    rw [area_eq r hr0.le (by linarith)]
    positivity
  · set r := min (1/2) (δ / (8 * π ^ 2)) with hr
    have hr0 : 0 < r := lt_min (by norm_num) (by positivity)
    have hr1 : r ≤ 1/2 := min_le_left _ _
    have hrδ : r ≤ δ / (8 * π ^ 2) := min_le_right _ _
    have hnn : (0:ℝ) ≤ 1 - r ^ 2 := by nlinarith
    have hs1 : Real.sqrt (1 - r ^ 2) ≤ 1 := by
      have h := Real.sqrt_le_sqrt (show 1 - r ^ 2 ≤ 1 by nlinarith)
      simpa using h
    have hsnn := Real.sqrt_nonneg (1 - r ^ 2)
    rw [area_eq r hr0.le (by linarith)]
    have hle : 4 * π ^ 2 * (r * Real.sqrt (1 - r ^ 2)) ≤ 4 * π ^ 2 * r := by
      have : r * Real.sqrt (1 - r ^ 2) ≤ r * 1 := by
        exact mul_le_mul_of_nonneg_left hs1 hr0.le
      nlinarith
    have h8 : (0:ℝ) < 8 * π ^ 2 := by positivity
    have hmul : r * (8 * π ^ 2) ≤ δ := by
      calc r * (8 * π ^ 2) ≤ (δ / (8 * π ^ 2)) * (8 * π ^ 2) :=
            mul_le_mul_of_nonneg_right hrδ h8.le
        _ = δ := by field_simp
    nlinarith
