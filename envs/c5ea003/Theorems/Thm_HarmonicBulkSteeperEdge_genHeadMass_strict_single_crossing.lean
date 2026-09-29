-- Prove2me | Theorems.Thm_HarmonicBulkSteeperEdge_genHeadMass_strict_single_crossing
-- name    : HarmonicBulkSteeperEdge.genHeadMass_strict_single_crossing
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:43:34.171885+00:00
-- url     : https://prove2.me/theorems/cac22e2c-72c9-4b45-9136-2af2b4f5240a
-- title:
--   Strict single-crossing for a general mixture.
-- statement:
--   **Strict single-crossing for a general mixture.**  If a pure power law with exponent `c`
--   matches the head mass of a heterogeneous mixture on the window `{1, …, m₂}`, it reports
--   strictly less head mass on every narrower window.
--
--   ```lean
--   theorem HarmonicBulkSteeperEdge.genHeadMass_strict_single_crossing{s : Finset ι} {w e : ι → ℝ} {c : ℝ}
--       (hw : ∀ i ∈ s, 0 < w i) {p q : ι} (hp : p ∈ s) (hq : q ∈ s) (hpq : e p ≠ e q)
--       {m₁ m₂ n : ℕ} (hm₁ : 1 ≤ m₁) (h₁₂ : m₁ < m₂) (h₂n : m₂ < n)
--       (hmatch : headMass c n m₂ = genHeadMass s w e n m₂) :
--       headMass c n m₁ < genHeadMass s w e n m₁ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/GeneralMixtureWindowLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/GeneralMixtureWindowLaw.lean#L146

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

theorem HarmonicBulkSteeperEdge.genHeadMass_strict_single_crossing{s : Finset ι} {w e : ι → ℝ} {c : ℝ}
    (hw : ∀ i ∈ s, 0 < w i) {p q : ι} (hp : p ∈ s) (hq : q ∈ s) (hpq : e p ≠ e q)
    {m₁ m₂ n : ℕ} (hm₁ : 1 ≤ m₁) (h₁₂ : m₁ < m₂) (h₂n : m₂ < n)
    (hmatch : headMass c n m₂ = genHeadMass s w e n m₂) :
    headMass c n m₁ < genHeadMass s w e n m₁ := by sorry
