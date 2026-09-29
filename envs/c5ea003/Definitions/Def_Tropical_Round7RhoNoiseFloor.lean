-- Prove2me | Definitions.Def_Tropical_Round7RhoNoiseFloor
-- name    : Tropical_Round7RhoNoiseFloor
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:27.223095+00:00
-- url     : https://prove2.me/theorems/c3f95117-27ef-464b-a172-3f66b1ba82db
-- title:
--   Aether Catalog definitions — Tropical_Round7RhoNoiseFloor
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.Round7RhoNoiseFloor`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/Round7RhoNoiseFloor.lean by skeleton subtraction
import Mathlib

/-!
# Round-7 closure STATICRHO: scoping the noise-floor principle

Experiment 326 measured that the *correlated* sample set produced by the static
rho walk `x ↦ x² + 1 (mod N)` has factor-bearing density far above the
`N^{-1/2}` noise floor, and concluded that the noise-floor principle must be
scoped to **atomic uniform primitives**.  This file proves the three arithmetic
facts that make that refinement precise.

* `rhoZ_iterate_modEq` : the rho walk **commutes with reduction**: congruent
  seeds stay congruent, so the walk mod `N` covers a walk mod `p` — the source
  of the correlation.
* `exists_collision_mod_p` : by pigeonhole the walk mod `p` **collides within
  `p + 1` steps**, so among the first `p + 1` correlated samples a
  factor-bearing pair always exists (density `≥ 2/(p+1)p`, unconditionally,
  with no probabilistic hypothesis at all).
* `gcd_extract_of_dvd_sub` : a collision mod `p` that is *not* a collision mod
  `N` **extracts the factor**: `gcd(xᵢ - xⱼ, N) = p`.
* `rho_collision_extracts_factor` : the three combined — the correctness core of
  Pollard's rho.
* `aggregation_cost` : the escape is paid for by aggregation: extracting a
  factor from `T` correlated samples requires the `T(T-1)/2` pairwise gcds,
  which for `T = p + 1` already exceeds the `p` trial divisions.  This is the
  precise sense in which the correlated sample set does not beat the floor.

Contrast with `Catalog/Tropical/Round7ZeroDivisorGraph.lean`, where the atomic
uniform primitive is shown to succeed with probability at most `2/p`.
-/

namespace Round7Rho

/-! ## 1. The rho map and its compatibility with reduction -/

/-- The static rho map `x ↦ x² + 1`, taken over `ℤ` so that gcd extraction makes
sense on differences of iterates. -/
def rhoZ (x : ℤ) : ℤ := x ^ 2 + 1



/-! ## 2. The collision: pigeonhole on the reduced walk -/


/-! ## 3. Extraction: a one-sided collision reveals the factor -/



/-! ## 4. The aggregation price -/



end Round7Rho


