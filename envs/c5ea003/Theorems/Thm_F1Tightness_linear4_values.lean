-- Prove2me | Theorems.Thm_F1Tightness_linear4_values
-- name    : F1Tightness.linear4_values
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:26:18.7932+00:00
-- url     : https://prove2.me/theorems/29c57193-4c85-4ead-ba87-16bc24dd2892
-- title:
--   The linear profile `(0.4, 0.3, 0.2, 0.1)` on four cells: a fully explicit
-- statement:
--   The linear profile `(0.4, 0.3, 0.2, 0.1)` on four cells: a fully explicit
--   instance of the identity chain, with `Λ = 2/3`, `Θ = 4/5`, `X = 5/4`,
--   `S_asc = 3/2` and `bound = 15/8 = X · S_asc`.
--
--   ```lean
--   theorem F1Tightness.linear4_values:
--       scanCost (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10) = 2 ∧
--       revCost (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10) = 3 ∧
--       Lam (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10) = 2 / 3 ∧
--       Theta (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10) = 4 / 5 ∧
--       gapX (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10) = 5 / 4 ∧
--       boundF1 (Lam (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10))
--           (Theta (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10)) 1
--         = gapX (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10) *
--             Sasc (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/F1TightnessSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/F1TightnessSharpness.lean#L168

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



/-! ## A worked rational example -/

theorem F1Tightness.linear4_values:
    scanCost (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10) = 2 ∧
    revCost (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10) = 3 ∧
    Lam (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10) = 2 / 3 ∧
    Theta (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10) = 4 / 5 ∧
    gapX (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10) = 5 / 4 ∧
    boundF1 (Lam (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10))
        (Theta (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10)) 1
      = gapX (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10) *
          Sasc (fun i : Fin 4 => (4 - ((i : ℕ) : ℝ)) / 10) := by sorry
