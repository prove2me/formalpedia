-- Prove2me | Definitions.Def_Evergreen_OmegaTower_Basic
-- name    : Evergreen_OmegaTower_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:37:58.061243+00:00
-- url     : https://prove2.me/theorems/75c5b0da-4d16-4ce4-a322-73abdc2f03f3
-- title:
--   Aether Catalog definitions — Evergreen_OmegaTower_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.OmegaTower.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/OmegaTower/Basic.lean by skeleton subtraction
import Mathlib

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

/-- The omega tower: `omegaTower n` is the n-th iterated exponential tower of ω.
    - `omegaTower 0 = 1`
    - `omegaTower 1 = ω`
    - `omegaTower 2 = ω^ω`
    - `omegaTower 3 = ω^(ω^ω)`
    - etc. -/
def omegaTower : ℕ → Ordinal.{0}
  | 0 => 1
  | n + 1 => omega0 ^ omegaTower n

/-- ε₀ (epsilon-zero): the least fixed point of `ω ^ ·` above 0.
    This is the supremum of the omega tower and satisfies ω^(ε₀) = ε₀. -/
noncomputable def epsilon0 : Ordinal.{0} := Ordinal.nfp (omega0 ^ ·) 0

/-! ## Basic Values -/


/-! ## Key Normal Function -/



/-! ## Strict Monotonicity of the Tower -/





/-! ## Boundedness by ε₀ -/



/-! ## The Fixed-Point Property -/


/-! ## Minimality of ε₀ -/


/-! ## ε₀ is a limit ordinal -/




end


