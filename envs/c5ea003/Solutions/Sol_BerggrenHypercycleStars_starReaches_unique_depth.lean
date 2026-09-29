-- Prove2me | solution 1 for BerggrenHypercycleStars.starReaches_unique_depth
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:17:07.593536+00:00
-- url     : https://prove2.me/submissions/e3f8dfb3-9c6a-4b90-bd95-b20f84ee3bcb

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








/-! ## Part 2. The three Berggren moves in star coordinates -/




theorem isStarPair_starL {u v : ℕ} (h : IsStarPair u v) : IsStarPair (u + v) v := by
  obtain ⟨hu, hv, hcop, hodd⟩ := h
  exact ⟨by omega, hv, Nat.coprime_add_self_left.mpr hcop, hodd⟩

theorem isStarPair_starM {u v : ℕ} (h : IsStarPair u v) : IsStarPair (u + v) (2 * u + v) := by
  obtain ⟨hu, hv, hcop, hodd⟩ := h
  refine ⟨by omega, by omega, ?_, by omega⟩
  have h2 : Nat.Coprime (u + v) u := by
    rw [Nat.add_comm]
    exact Nat.coprime_add_self_left.mpr (Nat.coprime_comm.mp hcop)
  have h3 : 2 * u + v = (u + v) + u := by ring
  rw [h3]
  exact Nat.coprime_self_add_right.mpr h2

theorem isStarPair_starR {u v : ℕ} (h : IsStarPair u v) : IsStarPair u (2 * u + v) := by
  obtain ⟨hu, hv, hcop, hodd⟩ := h
  exact ⟨hu, by omega, (Nat.coprime_mul_right_add_right u v 2).mpr hcop, by omega⟩

/-! ## Part 3. Reachability: completeness and uniqueness of depth -/


/-- **Soundness.** Everything reachable is a star pair. -/
theorem isStarPair_of_starReaches {p : ℕ × ℕ} {k : ℕ} (h : StarReaches p k) :
    IsStarPair p.1 p.2 := by
  induction h with
  | root => exact ⟨one_pos, one_pos, Nat.coprime_one_left 1, rfl⟩
  | l _ ih => exact isStarPair_starL ih
  | m _ ih => exact isStarPair_starM ih
  | r _ ih => exact isStarPair_starR ih




theorem starReaches_zero {p : ℕ × ℕ} (h : StarReaches p 0) : p = (1, 1) := by
  cases h with
  | root => rfl

/-- Inversion: a node at depth `k+1` is the image of a node at depth `k` under one of the three
moves. -/
theorem starReaches_succ {p : ℕ × ℕ} {k : ℕ} (h : StarReaches p (k + 1)) :
    ∃ q, StarReaches q k ∧ (p = starL q ∨ p = starM q ∨ p = starR q) := by
  cases h with
  | l hq => exact ⟨_, hq, Or.inl rfl⟩
  | m hq => exact ⟨_, hq, Or.inr (Or.inl rfl)⟩
  | r hq => exact ⟨_, hq, Or.inr (Or.inr rfl)⟩


/-! ## Part 4. The radial coordinate in star coordinates -/




open BerggrenHypercycleStars in
theorem solution: ∀ s : ℕ, ∀ p : ℕ × ℕ, p.1 + p.2 ≤ s → ∀ j k : ℕ,
    StarReaches p j → StarReaches p k → j = k := by
  intro s
  induction s with
  | zero =>
    intro p hp j k hj _
    exact absurd hp (by have := (isStarPair_of_starReaches hj).posu; omega)
  | succ s ih =>
    intro p hp j k hj hk
    match j, k with
    | 0, 0 => rfl
    | 0, (k + 1) =>
      exfalso
      have hp1 : p = (1, 1) := starReaches_zero hj
      obtain ⟨q, hq, hcase⟩ := starReaches_succ hk
      have hqs := isStarPair_of_starReaches hq
      have h1 := hqs.posu
      have h2 := hqs.posv
      rcases hcase with hc | hc | hc <;>
        · rw [hp1] at hc
          simp only [BerggrenHypercycleStars.starL, BerggrenHypercycleStars.starM,
            BerggrenHypercycleStars.starR, Prod.mk.injEq] at hc
          omega
    | (j + 1), 0 =>
      exfalso
      have hp1 : p = (1, 1) := starReaches_zero hk
      obtain ⟨q, hq, hcase⟩ := starReaches_succ hj
      have hqs := isStarPair_of_starReaches hq
      have h1 := hqs.posu
      have h2 := hqs.posv
      rcases hcase with hc | hc | hc <;>
        · rw [hp1] at hc
          simp only [BerggrenHypercycleStars.starL, BerggrenHypercycleStars.starM,
            BerggrenHypercycleStars.starR, Prod.mk.injEq] at hc
          omega
    | (j + 1), (k + 1) =>
      obtain ⟨q, hq, hcq⟩ := starReaches_succ hj
      obtain ⟨q', hq', hcq'⟩ := starReaches_succ hk
      have hqs := isStarPair_of_starReaches hq
      have hqs' := isStarPair_of_starReaches hq'
      have h1 := hqs.posu
      have h2 := hqs.posv
      have h3 := hqs'.posu
      have h4 := hqs'.posv
      have h5 := hqs.odd
      have h6 := hqs'.odd
      have hqq : q = q' := by
        rcases hcq with hc | hc | hc <;> rcases hcq' with hc' | hc' | hc' <;>
          · rw [hc'] at hc
            simp only [BerggrenHypercycleStars.starL, BerggrenHypercycleStars.starM,
            BerggrenHypercycleStars.starR, Prod.mk.injEq] at hc
            rw [Prod.ext_iff]
            omega
      subst hqq
      have hsum : q.1 + q.2 ≤ s := by
        rcases hcq with hc | hc | hc <;>
          · rw [hc] at hp
            simp only [BerggrenHypercycleStars.starL, BerggrenHypercycleStars.starM,
            BerggrenHypercycleStars.starR] at hp
            omega
      have := ih q hsum j k hq hq'
      omega
