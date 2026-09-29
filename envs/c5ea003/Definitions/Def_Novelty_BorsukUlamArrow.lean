-- Prove2me | Definitions.Def_Novelty_BorsukUlamArrow
-- name    : Novelty_BorsukUlamArrow
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:08:07.547972+00:00
-- url     : https://prove2.me/theorems/8549ba75-e404-4411-aaa1-2529f41b89e5
-- title:
--   Aether Catalog definitions — Novelty_BorsukUlamArrow
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.BorsukUlamArrow`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/BorsukUlamArrow.lean by skeleton subtraction
import Mathlib

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

namespace BorsukUlamArrow

open scoped Real
open Set

/-! ## Part I: one-dimensional Borsuk–Ulam and its social-choice reading -/




/-! ## Part II: contrarian disproof of "continuous ⟹ dictatorial"

We model the space of individual preferences as the real line `ℝ` (a contractible,
convex domain: e.g. positions on a one-dimensional political spectrum). A social
choice / aggregation rule for `n` agents is a map `(Fin n → ℝ) → ℝ`. -/

/-- The averaging aggregator: the social outcome is the mean of the `n` individual
positions. -/
noncomputable def avg (n : ℕ) (p : Fin n → ℝ) : ℝ := (∑ i, p i) / n








end BorsukUlamArrow


