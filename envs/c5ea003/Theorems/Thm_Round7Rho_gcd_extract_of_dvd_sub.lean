-- Prove2me | Theorems.Thm_Round7Rho_gcd_extract_of_dvd_sub
-- name    : Round7Rho.gcd_extract_of_dvd_sub
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:37:56.219508+00:00
-- url     : https://prove2.me/theorems/3a4aea89-5540-48d4-a03d-648d93337a4a
-- title:
--   Extraction lemma.
-- statement:
--   **Extraction lemma.** If `p` divides the difference of two samples but `q`
--   does not, the gcd with `N = pq` is exactly `p`.
--
--   ```lean
--   theorem Round7Rho.gcd_extract_of_dvd_sub{p q : ℕ} (hp : p.Prime) (hq : q.Prime) {d : ℤ}
--       (hpd : (p : ℤ) ∣ d) (hqd : ¬ ((q : ℤ) ∣ d)) : Int.gcd d (p * q : ℕ) = p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/Round7RhoNoiseFloor.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/Round7RhoNoiseFloor.lean#L78

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


/-! ## 3. Extraction: a one-sided collision reveals the factor -/

theorem Round7Rho.gcd_extract_of_dvd_sub{p q : ℕ} (hp : p.Prime) (hq : q.Prime) {d : ℤ}
    (hpd : (p : ℤ) ∣ d) (hqd : ¬ ((q : ℤ) ∣ d)) : Int.gcd d (p * q : ℕ) = p := by sorry
