-- Prove2me | Theorems.Thm_EMLFixedPoint_exists_unique_fixedPoint_and_converges
-- name    : EMLFixedPoint.exists_unique_fixedPoint_and_converges
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:48:36.849436+00:00
-- url     : https://prove2.me/theorems/c4d4e68b-2ce6-4558-bf40-77b057435cc3
-- title:
--   Banach fixed-point theorem for the EML update, including uniqueness,
-- statement:
--   Banach fixed-point theorem for the EML update, including uniqueness,
--   convergence of every orbit in the invariant interval, and an explicit geometric
--   error estimate.
--
--   ```lean
--   theorem EMLFixedPoint.exists_unique_fixedPoint_and_converges    {a c L U q : ℝ} (hpos : 0 < L + c)
--       (hq0 : 0 ≤ q) (hq1 : q < 1) (hderiv : Real.exp a / (L + c) ≤ q)
--       (hmap : MapsTo (emlMap a c) (Icc L U) (Icc L U)) (x₀ : ℝ) (hx₀ : x₀ ∈ Icc L U) :
--       ∃ xstar ∈ Icc L U,
--         emlMap a c xstar = xstar ∧
--         (∀ y ∈ Icc L U, emlMap a c y = y → y = xstar) ∧
--         Tendsto (fun n => (emlMap a c)^[n] x₀) atTop (𝓝 xstar) ∧
--         ∀ n : ℕ, dist ((emlMap a c)^[n] x₀) xstar ≤
--           dist x₀ (emlMap a c x₀) * q ^ n / (1 - q) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/EML/FixedPointIteration.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/EML/FixedPointIteration.lean#L72

-- Thm stub generated from Applications/EML/FixedPointIteration.lean
import Mathlib
import Definitions.Def_Applications_EML_FixedPointIteration

/-!
# Fixed points of an exponential--logarithmic iteration

This file studies `x ↦ exp a * log (x + c)`.  The unrestricted test claim from
this research question is false: even with `0 < a < 1` and `0 < c < 1`, a fixed
point need not exist.  We prove this for `a = log 2`, `c = 1/2` on the natural
logarithmic domain.

The positive result is the precise contraction theorem suggested by the question.
On a closed invariant interval `[L,U]`, if `L+c>0` and
`exp a / (L+c) ≤ q < 1`, the map has a unique fixed point in the interval;
every iteration starting there converges to it with Banach's geometric error bound.
-/

noncomputable section

open Real Set Filter Function Topology

open EMLFixedPoint

theorem EMLFixedPoint.exists_unique_fixedPoint_and_converges    {a c L U q : ℝ} (hpos : 0 < L + c)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hderiv : Real.exp a / (L + c) ≤ q)
    (hmap : MapsTo (emlMap a c) (Icc L U) (Icc L U)) (x₀ : ℝ) (hx₀ : x₀ ∈ Icc L U) :
    ∃ xstar ∈ Icc L U,
      emlMap a c xstar = xstar ∧
      (∀ y ∈ Icc L U, emlMap a c y = y → y = xstar) ∧
      Tendsto (fun n => (emlMap a c)^[n] x₀) atTop (𝓝 xstar) ∧
      ∀ n : ℕ, dist ((emlMap a c)^[n] x₀) xstar ≤
        dist x₀ (emlMap a c x₀) * q ^ n / (1 - q) := by sorry
