-- Prove2me | solution 1 for Round7Rho.gcd_extract_of_dvd_sub
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:27:13.529846+00:00
-- url     : https://prove2.me/submissions/8aade563-b0a7-42de-bb48-b66a9d7969bc

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
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) {d : ℤ}
    (hpd : (p : ℤ) ∣ d) (hqd : ¬ ((q : ℤ) ∣ d)) : Int.gcd d (p * q : ℕ) = p := by
  have hgN : Int.gcd d (p * q : ℕ) ∣ p * q := by
    have h := Int.gcd_dvd_right d ((p * q : ℕ) : ℤ)
    exact_mod_cast h
  have hgd : ((Int.gcd d (p * q : ℕ) : ℕ) : ℤ) ∣ d := Int.gcd_dvd_left _ _
  have hpg : p ∣ Int.gcd d (p * q : ℕ) := by
    have h1 : (p : ℤ) ∣ ((p * q : ℕ) : ℤ) := by push_cast; exact ⟨q, rfl⟩
    have h2 := Int.dvd_gcd hpd h1
    exact_mod_cast h2
  obtain ⟨k, hk⟩ := hpg
  have hkq : k ∣ q := by
    have : p * k ∣ p * q := hk ▸ hgN
    exact (mul_dvd_mul_iff_left hp.pos.ne').mp this
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq k hkq) with h1 | h1
  · rw [hk, h1, mul_one]
  · exfalso
    apply hqd
    have hqg : (q : ℤ) ∣ ((Int.gcd d (p * q : ℕ) : ℕ) : ℤ) := by
      rw [hk, h1]
      exact ⟨(p : ℤ), by push_cast; ring⟩
    exact hqg.trans hgd
