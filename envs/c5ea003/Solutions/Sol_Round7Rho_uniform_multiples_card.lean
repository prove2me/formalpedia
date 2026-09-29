-- Prove2me | solution 1 for Round7Rho.uniform_multiples_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:27:13.981553+00:00
-- url     : https://prove2.me/submissions/83024150-a603-4b6f-ad9c-aed4c1d31505

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
theorem solution{p q : ℕ} (hp : 0 < p) :
    ((Finset.Ioo 0 (p * q)).filter (fun x => p ∣ x)).card * p = p * q - p := by
  have himg : (Finset.Ioo 0 (p * q)).filter (fun x => p ∣ x)
      = (Finset.Ioo 0 q).image (p * ·) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_image]
    constructor
    · rintro ⟨⟨hx0, hxN⟩, k, rfl⟩
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp at hx0
        · exact hk
      · exact lt_of_mul_lt_mul_left hxN (Nat.zero_le p)
    · rintro ⟨k, ⟨hk0, hkq⟩, rfl⟩
      exact ⟨⟨Nat.mul_pos hp hk0, by nlinarith⟩, ⟨k, rfl⟩⟩
  have hinj : Function.Injective (fun k : ℕ => p * k) := fun a b hab =>
    Nat.eq_of_mul_eq_mul_left hp hab
  rw [himg, Finset.card_image_of_injective _ hinj, Nat.card_Ioo]
  have hq0 : q - 0 - 1 = q - 1 := by omega
  rw [hq0, Nat.sub_mul, one_mul, Nat.mul_comm q p]
