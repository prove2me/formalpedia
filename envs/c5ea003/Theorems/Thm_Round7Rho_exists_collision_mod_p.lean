-- Prove2me | Theorems.Thm_Round7Rho_exists_collision_mod_p
-- name    : Round7Rho.exists_collision_mod_p
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:37:59.509469+00:00
-- url     : https://prove2.me/theorems/8aa33687-6406-4261-8ef3-a056d6fbce0f
-- title:
--   Collision within `p + 1` steps.
-- statement:
--   **Collision within `p + 1` steps.** For any seed, two of the first `p + 1`
--   iterates of the rho walk agree modulo `p`.  No randomness and no heuristic is
--   involved: the reduced state space has only `p` elements.
--
--   ```lean
--   theorem Round7Rho.exists_collision_mod_p(p : ℕ) (hp : 0 < p) (x₀ : ℤ) :
--       ∃ i j : ℕ, i < j ∧ j ≤ p ∧ (p : ℤ) ∣ (rhoZ^[j] x₀ - rhoZ^[i] x₀) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/Round7RhoNoiseFloor.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/Round7RhoNoiseFloor.lean#L56

-- Thm stub generated from Tropical/Round7RhoNoiseFloor.lean
import Mathlib
import Definitions.Def_Tropical_Round7RhoNoiseFloor

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

open Round7Rho

/-! ## 1. The rho map and its compatibility with reduction -/




/-! ## 2. The collision: pigeonhole on the reduced walk -/

theorem Round7Rho.exists_collision_mod_p(p : ℕ) (hp : 0 < p) (x₀ : ℤ) :
    ∃ i j : ℕ, i < j ∧ j ≤ p ∧ (p : ℤ) ∣ (rhoZ^[j] x₀ - rhoZ^[i] x₀) := by sorry
