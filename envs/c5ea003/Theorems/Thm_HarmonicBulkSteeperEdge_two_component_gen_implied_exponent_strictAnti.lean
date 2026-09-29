-- Prove2me | Theorems.Thm_HarmonicBulkSteeperEdge_two_component_gen_implied_exponent_strictAnti
-- name    : HarmonicBulkSteeperEdge.two_component_gen_implied_exponent_strictAnti
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:45:40.126474+00:00
-- url     : https://prove2.me/theorems/96033677-9698-4bbd-bdde-85c0376304b4
-- title:
--   The two-component window law as an instance of the general one.
-- statement:
--   **The two-component window law as an instance of the general one.**  Recovering
--   `implied_exponent_strictAnti` from `gen_implied_exponent_strictAnti` confirms that the
--   generalisation is faithful.
--
--   ```lean
--   theorem HarmonicBulkSteeperEdge.two_component_gen_implied_exponent_strictAnti{w a b c₁ c₂ : ℝ} (hw0 : 0 < w)
--       (hw1 : w < 1) (hab : a < b) {m₁ m₂ n : ℕ} (hm₁ : 1 ≤ m₁) (h₁₂ : m₁ < m₂) (h₂n : m₂ < n)
--       (h₁ : headMass c₁ n m₁ = mixHeadMass w a b n m₁)
--       (h₂ : headMass c₂ n m₂ = mixHeadMass w a b n m₂) :
--       c₂ < c₁ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/GeneralMixtureWindowLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/GeneralMixtureWindowLaw.lean#L262

-- Thm stub generated from Probability/GeneralMixtureWindowLaw.lean
import Mathlib
import Definitions.Def_Probability_GeneralMixtureWindowLaw
import Definitions.Def_Probability_HarmonicBulkSteeperEdge
/-
  # The window law for arbitrary exponent heterogeneity

  `Probability.HarmonicBulkSteeperEdgeStrict` proves that the window-implied exponent of a
  *two-component* power-law kernel is strictly antitone in the window width.  Nothing in
  that proof used the number two: it used only that the kernel-to-power-law ratio is
  strictly convex in `log k`.  This file carries the argument out for an arbitrary finite
  positive combination of power laws

  `k ↦ ∑ i ∈ s, w i · k ^ (-e i)`,

  and shows that the antitone window law is a signature of *exponent heterogeneity as
  such*: it holds as soon as two of the exponents differ, with any number of components and
  any positive weights.

  * `genRatio_strict_log_convex` — strict convexity in the logarithmic index, from the
    two-power lemmas of `HarmonicBulkSteeperEdgeStrict` plus a strict sum comparison.
  * `genRatio_lt_of_crossed_strict` — strict no-return past a weak crossing.
  * `genHeadMass_strict_single_crossing` — a pure power law matching the mixture's head mass
    on a window reports strictly less head mass on every narrower window.
  * `gen_implied_exponent_strictAnti` — the window-implied exponent is strictly antitone.
  * `two_component_gen_implied_exponent_strictAnti` — the two-component theorem recovered as
    the instance `s = {0, 1}`, confirming the generalisation is faithful.
-/

open Finset

open HarmonicBulkSteeperEdge

variable {ι : Type*}

/-! ## A finite positive combination of power laws -/








/-! ## Strict log-convexity for an arbitrary heterogeneous mixture -/




/-! ## The window law -/

theorem HarmonicBulkSteeperEdge.two_component_gen_implied_exponent_strictAnti{w a b c₁ c₂ : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) (hab : a < b) {m₁ m₂ n : ℕ} (hm₁ : 1 ≤ m₁) (h₁₂ : m₁ < m₂) (h₂n : m₂ < n)
    (h₁ : headMass c₁ n m₁ = mixHeadMass w a b n m₁)
    (h₂ : headMass c₂ n m₂ = mixHeadMass w a b n m₂) :
    c₂ < c₁ := by sorry
