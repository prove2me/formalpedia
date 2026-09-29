-- Prove2me | Theorems.Thm_epsilon0_isSuccLimit
-- name    : epsilon0_isSuccLimit
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T16:53:55.963025+00:00
-- url     : https://prove2.me/theorems/a4fb79fc-c966-42b7-b8c7-2338a4272b19
-- title:
--   ε₀ is a limit ordinal (not zero, not a successor).
-- statement:
--   ε₀ is a limit ordinal (not zero, not a successor).
--
--       **Proof**: If `a ⋖ ε₀` (a is covered by ε₀, i.e., a is an immediate
--       predecessor), then `a < ε₀`. Since `ω^·` is a normal function,
--       `a ≤ ω^a`. If `a = ω^a`, then `a` is a fixed point of `ω^·`, so
--       `ε₀ ≤ a`, contradicting `a < ε₀`. Thus `a < ω^a`. But also
--       `ω^a < ω^(ε₀) = ε₀` by strict monotonicity. This gives
--       `a < ω^a < ε₀`, contradicting `a ⋖ ε₀`.
--
--   ```lean
--   theorem epsilon0_isSuccLimit: Order.IsSuccLimit epsilon0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Evergreen/OmegaTower/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Evergreen/OmegaTower/Basic.lean#L134

-- Thm stub generated from Evergreen/OmegaTower/Basic.lean
import Mathlib
import Definitions.Def_Evergreen_OmegaTower_Basic

/-!
# The Omega Tower: Climbing to ε₀

## Overview

The **omega tower** is the sequence of ordinals defined by iterating ordinal
exponentiation with base ω:

  Level 0:  1
  Level 1:  ω
  Level 2:  ω^ω
  Level 3:  ω^(ω^ω)
  Level 4:  ω^(ω^(ω^ω))
    ⋮

Each level dwarfs the one below—not just in the sense of being larger, but in
the sense of being *exponentially* larger in the ordinal hierarchy. Yet this
tower has a ceiling: the ordinal **ε₀** (epsilon-zero), defined as the smallest
ordinal satisfying ω^(ε₀) = ε₀.

ε₀ is, in a precise sense, "the first ordinal you can't name using finite
towers of omega." It plays a crucial role in proof theory—it measures the
strength of Peano Arithmetic (Gentzen 1936).

## Main Definitions

* `omegaTower n` — the n-th level of the omega tower
* `epsilon0` — the ordinal ε₀ = nfp (ω ^ ·) 0

## Main Theorems

* `omegaTower_strictMono` — each level is strictly larger than the last
* `omegaTower_lt_epsilon0` — every finite level is below ε₀
* `epsilon0_fixed_point` — ω^(ε₀) = ε₀
* `epsilon0_le_of_fixed_point` — ε₀ is the *least* fixed point ≥ 0
* `epsilon0_isSuccLimit` — ε₀ is a limit ordinal
-/

noncomputable section

open Ordinal

/-! ## The Omega Tower -/



/-! ## Basic Values -/


/-! ## Key Normal Function -/



/-! ## Strict Monotonicity of the Tower -/





/-! ## Boundedness by ε₀ -/



/-! ## The Fixed-Point Property -/


/-! ## Minimality of ε₀ -/


/-! ## ε₀ is a limit ordinal -/

theorem epsilon0_isSuccLimit: Order.IsSuccLimit epsilon0 := by sorry
