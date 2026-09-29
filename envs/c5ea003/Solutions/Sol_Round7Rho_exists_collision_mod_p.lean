-- Prove2me | solution 1 for Round7Rho.exists_collision_mod_p
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:27:13.0122+00:00
-- url     : https://prove2.me/submissions/02c1df78-2748-4793-9f1b-ade12826c6a8

-- Sol generated from Tropical/Round7RhoNoiseFloor.lean
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



/-! ## 4. The aggregation price -/




open Round7Rho in
theorem solution(p : ℕ) (hp : 0 < p) (x₀ : ℤ) :
    ∃ i j : ℕ, i < j ∧ j ≤ p ∧ (p : ℤ) ∣ (rhoZ^[j] x₀ - rhoZ^[i] x₀) := by
  haveI : NeZero p := ⟨hp.ne'⟩
  -- the map `t ↦ x_t mod p` on `Fin (p+1)` cannot be injective
  have hcard : Fintype.card (ZMod p) < Fintype.card (Fin (p + 1)) := by
    simp [ZMod.card]
  obtain ⟨i, j, hij, hEq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun t : Fin (p + 1) => ((rhoZ^[t.1] x₀ : ℤ) : ZMod p))
      hcard
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = j => hij (Fin.ext h)) with h | h
  · refine ⟨i.1, j.1, h, by omega, ?_⟩
    have := (ZMod.intCast_eq_intCast_iff' _ _ _).mp hEq.symm
    exact Int.ModEq.dvd this.symm
  · refine ⟨j.1, i.1, h, by omega, ?_⟩
    have := (ZMod.intCast_eq_intCast_iff' _ _ _).mp hEq
    exact Int.ModEq.dvd this.symm
