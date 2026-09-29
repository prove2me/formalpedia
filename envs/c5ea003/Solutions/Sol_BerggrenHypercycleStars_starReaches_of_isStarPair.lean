-- Prove2me | solution 1 for BerggrenHypercycleStars.starReaches_of_isStarPair
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:17:06.956935+00:00
-- url     : https://prove2.me/submissions/50dddb48-9039-4645-892e-7d484dd84ccc

-- Sol generated from Cryptography/BerggrenStars/StarCoordinates.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars
import Definitions.Def_Cryptography_BerggrenStars_StarCoordinates

/-!
# Star coordinates: the Berggren tree seen from the two boundary stars

`Cryptography.BerggrenStars.HypercycleStars` shows that a Berggren node `z(m,n) = (n+i)/m`
sits at distance `arsinh n` from the geodesic over the boundary point `0` and at distance
`arsinh (m-n)` from the geodesic over the boundary point `1`. So the pair

  `(u, v) = (n, m - n)`

is exactly the pair of *star indices* of the node — one index per radiating star. This file
develops the tree entirely in these coordinates, and the result is markedly cleaner than in
Euclid coordinates.

## Main results

* `starPoint_charges` : `(u, v)` really is the pair of hyperbolic star charges,
  `sinh d₀ = u` and `sinh d₁ = v`.
* `node_eq_of_charges` : **the two star charges determine the node**; the star picture is a
  faithful coordinate system on the tree.
* `isSeed_iff_isStarPair` : the Euclid-seed conditions `0 < n < m`, `gcd(m,n) = 1`, `m + n` odd
  become the conditions `0 < u`, `0 < v`, `gcd(u,v) = 1`, `v` odd.
* `isStarPair_starL/M/R` : the three Berggren moves act as
  `(u,v) ↦ (u+v, v)`, `(u,v) ↦ (u+v, 2u+v)`, `(u,v) ↦ (u, 2u+v)` and preserve star pairs.
* `exists_depth_of_isStarPair` : **completeness** — every star pair is reached from the root
  `(1,1)`, by a descent whose trichotomy is `u > v`, `u < v < 2u`, `v > 2u`.
* `starReaches_unique_depth` : **it is a tree** — the depth at which a star pair is reached is
  unique, so the depth function is well defined.
* `cosh_dist_starPoint` : the radial coordinate in star coordinates,
  `cosh d = ((u+v)² + u² + 1)/(2(u+v))`.
-/

open BerggrenHypercycleStars

open Real UpperHalfPlane

/-! ## Part 1. Star coordinates and their charges -/





/-- Descent tool: if `u` and `v` are non-negative integer combinations of `a` and `b`, then
coprimality of `u, v` forces coprimality of `a, b`. -/
theorem coprime_of_comb (a b u v c₁ c₂ d₁ d₂ : ℕ) (hu : u = c₁ * a + c₂ * b)
    (hv : v = d₁ * a + d₂ * b) (h : Nat.Coprime u v) : Nat.Coprime a b := by
  have h1 : Nat.gcd a b ∣ u := by
    rw [hu]
    exact Nat.dvd_add ((Nat.gcd_dvd_left a b).mul_left c₁) ((Nat.gcd_dvd_right a b).mul_left c₂)
  have h2 : Nat.gcd a b ∣ v := by
    rw [hv]
    exact Nat.dvd_add ((Nat.gcd_dvd_left a b).mul_left d₁) ((Nat.gcd_dvd_right a b).mul_left d₂)
  have hdvd : Nat.gcd a b ∣ Nat.gcd u v := Nat.dvd_gcd h1 h2
  rw [h] at hdvd
  exact Nat.dvd_one.mp hdvd



/-! ## Part 2. The three Berggren moves in star coordinates -/







/-! ## Part 3. Reachability: completeness and uniqueness of depth -/









/-! ## Part 4. The radial coordinate in star coordinates -/




open BerggrenHypercycleStars in
theorem solution: ∀ s u v : ℕ, u + v ≤ s → IsStarPair u v →
    ∃ k, StarReaches (u, v) k := by
  intro s
  induction s with
  | zero => intro u v hs h; exact absurd hs (by have := h.posu; omega)
  | succ s ih =>
    intro u v hs h
    obtain ⟨hu, hv, hcop, hodd⟩ := h
    rcases lt_trichotomy u v with hlt | heq | hgt
    · rcases lt_trichotomy v (2 * u) with h2 | h2 | h2
      · -- parent via `starM` : `(v - u, 2u - v)`
        have hp : IsStarPair (v - u) (2 * u - v) :=
          ⟨by omega, by omega,
            coprime_of_comb _ _ u v 1 1 2 1 (by omega) (by omega) hcop, by omega⟩
        obtain ⟨k, hk⟩ := ih (v - u) (2 * u - v) (by omega) hp
        refine ⟨k + 1, ?_⟩
        have he : starM (v - u, 2 * u - v) = (u, v) := by
          simp only [starM, Prod.mk.injEq]
          omega
        rw [← he]
        exact StarReaches.m hk
      · exact absurd hodd (by omega)
      · -- parent via `starR` : `(u, v - 2u)`
        have hp : IsStarPair u (v - 2 * u) :=
          ⟨hu, by omega, coprime_of_comb _ _ u v 1 0 2 1 (by omega) (by omega) hcop, by omega⟩
        obtain ⟨k, hk⟩ := ih u (v - 2 * u) (by omega) hp
        refine ⟨k + 1, ?_⟩
        have he : starR (u, v - 2 * u) = (u, v) := by
          simp only [starR, Prod.mk.injEq, true_and]
          omega
        rw [← he]
        exact StarReaches.r hk
    · -- `u = v` forces `u = v = 1` by coprimality: the root
      have hu1 : u = 1 := by
        have hg : Nat.gcd u v = 1 := hcop
        rw [← heq, Nat.gcd_self] at hg
        omega
      have he : (u, v) = (1, 1) := by
        simp only [Prod.mk.injEq]
        exact ⟨hu1, by omega⟩
      exact ⟨0, he ▸ StarReaches.root⟩
    · -- parent via `starL` : `(u - v, v)`
      have hp : IsStarPair (u - v) v :=
        ⟨by omega, hv, coprime_of_comb _ _ u v 1 1 0 1 (by omega) (by omega) hcop, hodd⟩
      obtain ⟨k, hk⟩ := ih (u - v) v (by omega) hp
      refine ⟨k + 1, ?_⟩
      have he : starL (u - v, v) = (u, v) := by
        simp only [BerggrenHypercycleStars.starL, Prod.mk.injEq, and_true]
        omega
      rw [← he]
      exact StarReaches.l hk
