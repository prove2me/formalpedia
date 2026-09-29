-- Prove2me | Theorems.Thm_BorsukUlamArrow_borsuk_ulam_1d
-- name    : BorsukUlamArrow.borsuk_ulam_1d
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:06:04.544393+00:00
-- url     : https://prove2.me/theorems/48d16de5-3929-4907-a969-bf95b3f74b91
-- title:
--   One-dimensional Borsuk–Ulam theorem.
-- statement:
--   **One-dimensional Borsuk–Ulam theorem.** A continuous `2π`-periodic function
--   `f : ℝ → ℝ` — that is, a continuous map from the circle `S¹` to `ℝ¹` — sends some
--   pair of antipodal points `x` and `x + π` to the same value.
--
--   ```lean
--   theorem BorsukUlamArrow.borsuk_ulam_1d(f : ℝ → ℝ) (hf : Continuous f)
--       (hper : ∀ x, f (x + 2 * Real.pi) = f x) :
--       ∃ x, f x = f (x + Real.pi) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BorsukUlamArrow.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BorsukUlamArrow.lean#L54

-- Thm stub generated from Novelty/BorsukUlamArrow.lean
import Mathlib
import Definitions.Def_Novelty_BorsukUlamArrow

/-!
# Borsuk–Ulam and Social Choice: the topological kernel and a contrarian disproof

This file investigates the conjecture that **Arrow's impossibility theorem is a
corollary of the Borsuk–Ulam theorem**, and that consequently *"any social choice
function on `n` alternatives is either discontinuous or dictatorial."*

We treat the claim in **contrarian** mode: we isolate the genuine topological
kernel that *is* true, and we **disprove** the over-strong conjecture.

## Part I — The topological kernel (positive results)

The honest mathematical content of the "preference sphere" picture, in the
lowest dimension, is the **one-dimensional Borsuk–Ulam theorem**: a continuous
`2π`-periodic function `f : ℝ → ℝ` (a continuous function on the circle
`S¹ = ℝ / 2πℤ`, i.e. `f : S¹ → ℝ¹`) must send some pair of antipodal points
`x`, `x + π` to the same value.

* `borsuk_ulam_1d` : `∃ x, f x = f (x + π)`.

Its social-choice reading is the genuine kernel of the description's
"contradiction with Pareto efficiency": one cannot continuously and *strictly*
prefer every profile over its antipode.

* `no_strict_antipodal_preference` : `¬ ∀ x, f (x + π) < f x`.
* `no_strict_antipodal_preference'` : `¬ ∀ x, f x < f (x + π)`.

## Part II — The contrarian disproof

The strong conjecture *"continuous ⟹ dictatorial"* is **false** once the space of
preferences is **contractible** (e.g. the real line), rather than a sphere. The
topological obstruction of Borsuk–Ulam/Chichilnisky genuinely requires the
non-contractible sphere topology; it says nothing about aggregation on a convex
domain. We exhibit an explicit **averaging** aggregator on `n ≥ 2` agents that is
simultaneously

* continuous (`avg_continuous`),
* unanimous / Pareto (`avg_unanimity`),
* anonymous, hence symmetric (`avg_anonymous`),
* **non-dictatorial** (`avg_not_dictatorial`),

packaged as `continuous_nondictatorial_aggregator_exists`. This directly refutes
the conjecture that every continuous aggregation rule is dictatorial.
-/

open BorsukUlamArrow

open scoped Real
open Set

/-! ## Part I: one-dimensional Borsuk–Ulam and its social-choice reading -/

theorem BorsukUlamArrow.borsuk_ulam_1d(f : ℝ → ℝ) (hf : Continuous f)
    (hper : ∀ x, f (x + 2 * Real.pi) = f x) :
    ∃ x, f x = f (x + Real.pi) := by sorry
