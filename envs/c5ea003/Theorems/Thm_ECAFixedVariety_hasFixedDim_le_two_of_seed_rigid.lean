-- Prove2me | Theorems.Thm_ECAFixedVariety_hasFixedDim_le_two_of_seed_rigid
-- name    : ECAFixedVariety.hasFixedDim_le_two_of_seed_rigid
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:31:29.494213+00:00
-- url     : https://prove2.me/theorems/bc82fa6f-fd8d-44a4-b69b-7eeb398ba1cb
-- title:
--   Seed rigidity caps the dimension at two.
-- statement:
--   **Seed rigidity caps the dimension at two.**  If a stationary configuration
--   is determined by its values at the two cells `0` and `1`, the fixed-point
--   variety cannot have dimension more than `2`, however large the ring is.
--
--   ```lean
--   theorem ECAFixedVariety.hasFixedDim_le_two_of_seed_rigid{rule n : ℕ} [NeZero n]
--       (hrig : ∀ s ∈ fixedSet rule n, s 0 = 0 → s 1 = 0 → s = 0) {d : ℕ}
--       (h : HasFixedDim rule n d) : d ≤ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ECAFixedVarietyCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ECAFixedVarietyCore.lean#L222

-- Thm stub generated from Novelty/ECAFixedVarietyCore.lean
import Mathlib
import Definitions.Def_Novelty_CellularAutomataAlgebraicGeometry
import Definitions.Def_Novelty_ECAFixedVarietyCore

/-!
# The fixed-point variety of an elementary cellular automaton

This file sets up the algebraic-geometry style framework in which the
"ECA complexity = dimension of the fixed-point variety" conjecture can be
*tested*, building directly on the Boolean local rules of
`Novelty.CellularAutomataAlgebraicGeometry`.

A cyclic configuration of size `n` is a function `ZMod n → ZMod 2`, i.e. a point
of the affine space `𝔸ⁿ_{𝔽₂}` (for `n = 0` this degenerates to the bi-infinite
configuration space `ℤ → ZMod 2`, which is why all statements below are stated
uniformly over `ZMod n`).  The *fixed-point variety* of Wolfram rule `rule` is

  `V(rule, n) = { s : ZMod n → ZMod 2 | step rule s = s }`,

the `𝔽₂`-points of the zero locus of the `n` cubic polynomials
`fᵣ(s_{i-1}, s_i, s_{i+1}) - s_i`.

## Main results

* `localRuleZ_ofBool` — the `ZMod 2`-valued local rule agrees with the Boolean
  local rule of the catalog file, so this is genuinely the same dynamics.
* `mem_fixedSet_iff` — pointwise description of the fixed-point variety.
* `fixedSet_rotate` — the variety is invariant under the shift, i.e. it is a
  cyclic subshift of finite type, not an arbitrary subset.
* `IsAdditive.fixedSubmodule` — for an *additive* rule the variety really is a
  linear subspace, so a dimension `HasFixedDim` is defined.
* `rule204_hasFixedDim`, `rule204_fixedSet_univ` — the identity rule (Wolfram
  class 1/2) attains the maximal dimension `n`.
* `rule0_hasFixedDim_zero` — the null rule has dimension `0`.
* `hasFixedDim_unique` — the dimension, when it exists, is well defined.
-/

open ECAFixedVariety

open CellularAutomataAlgebraicGeometry












/-! ### Periodicity transfer on the ring

Many fixed-point loci are governed by a spatial period `p`; when `p` is
invertible modulo the ring size the configuration is forced to be constant.
These generic lemmas are used for `p = 2` and `p = 3` below. -/

theorem ECAFixedVariety.hasFixedDim_le_two_of_seed_rigid{rule n : ℕ} [NeZero n]
    (hrig : ∀ s ∈ fixedSet rule n, s 0 = 0 → s 1 = 0 → s = 0) {d : ℕ}
    (h : HasFixedDim rule n d) : d ≤ 2 := by sorry
