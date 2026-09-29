-- Prove2me | Theorems.Thm_F1Tightness_gapX_stability
-- name    : F1Tightness.gapX_stability
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:25:55.377714+00:00
-- url     : https://prove2.me/theorems/483b27d3-6522-467d-a3e2-165f840aff94
-- title:
--   Hump-insensitivity.
-- statement:
--   **Hump-insensitivity.**  The slack factor is Lipschitz in the profile with
--   respect to the `L¹` distance: a perturbation of total mass `ε` moves `X` by at
--   most `M(M+1)ε/2`.  (Both costs are at least `1`, which is what makes the
--   denominators harmless.)
--
--   ```lean
--   theorem F1Tightness.gapX_stability{p q : Fin M → ℝ} (hp : ∀ i, 0 ≤ p i)
--       (hsump : ∑ i : Fin M, p i = 1) (hq : ∀ i, 0 ≤ q i) (hsumq : ∑ i : Fin M, q i = 1) :
--       |gapX p - gapX q| ≤ ((M : ℝ) + 1) / 2 * ((M : ℝ) * ∑ i : Fin M, |p i - q i|) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/F1TightnessSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/F1TightnessSharpness.lean#L126

-- Thm stub generated from Probability/F1TightnessSharpness.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessSharpness

/-!
# Sharpness over the prior class, stability, and the binding arm (paper 250)

`Probability.F1TightnessCore` proves that on a fixed front-loaded, non-flat
positional profile the F1 master bound is *never attained*: the slack factor
`X = C₀/c_asc` is strictly larger than one.  The natural objection is that the
inequality might then be improvable.  This file shows it is not: the bound is
**sharp over the prior class** even though it is unattainable on any fixed
non-flat pool.  This is the theorem-side closer named in the round-92
deliverable: sharpness must be posed over the class of priors, never as
tightness on one pool.

Main results.

* `twoCell` — the two-cell family `p_δ = (1/2 + δ, 1/2 − δ)`, antitone and
  non-flat for `0 < δ < 1/2`, with slack factor `X = (3/2)/(3/2 − δ)`.
* `twoCell_gapX`, `twoCell_slack_small` — the slack of `p_δ` tends to `1`.
* `sharp_over_prior_class` — for every `ε > 0` there is an admissible
  (antitone, non-flat) profile whose slack is `< 1 + ε`: the constant `1`
  cannot be improved uniformly over the prior class, yet
  `slack_never_attained` says no admissible profile reaches it.
* `gapX_stability` — the slack factor is Lipschitz in the profile for the `L¹`
  distance; this is the formal content of "hump-insensitivity": a bounded
  perturbation of the profile moves `X` by a bounded amount.
* `binding_arm` — with `k_bits = 0` and `q̂ ≥ 1` the first arm of the master
  bound `min(1/(ΛΘq̂), 2^k/(ΛΘ))` is the binding one, as booked.
-/

open Finset

open F1Tightness

/-! ## A two-cell family approaching flatness -/











/-! ## Stability of the slack factor ("hump-insensitivity") -/

variable {M : ℕ}

theorem F1Tightness.gapX_stability{p q : Fin M → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsump : ∑ i : Fin M, p i = 1) (hq : ∀ i, 0 ≤ q i) (hsumq : ∑ i : Fin M, q i = 1) :
    |gapX p - gapX q| ≤ ((M : ℝ) + 1) / 2 * ((M : ℝ) * ∑ i : Fin M, |p i - q i|) := by sorry
