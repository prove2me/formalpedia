-- Prove2me | solution 1 for GilbertLattice.no_edge_of_length_sqrt_prime_three_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:38:06.153703+00:00
-- url     : https://prove2.me/submissions/41db9d28-ee15-401d-8a33-e6b630151859

-- Sol generated from Shared/GilbertLatticeSumTwoSquares.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeSumTwoSquares
import Theorems.Thm_GilbertLattice_latticeSpectrum_eq_sums_of_two_squares

/-!
# A bridge: the conditioned Gilbert model and the two-square theorem

This file connects two areas that look unrelated at first sight:

* **continuum percolation on the square lattice** — Gilbert's disc model conditioned on
  `ℤ²`, where one point is placed in each cell of the grid and two points are joined
  when they are at distance `< R` (the model of `GilbertLatticeBasic.lean`), and
* **the arithmetic of sums of two squares** — Fermat's two-square theorem, the
  Brahmagupta–Fibonacci identity and the classification of the integers represented by
  the norm form `x² + y²` of the Gaussian integers.

The link is the family of *aligned* configurations, in which every point receives the
same offset `(s,t)` inside its cell: the point set is then a translate of `ℤ²`, so the
squared length of every edge of the Gilbert graph is an integer of the form `a² + b²`,
and conversely every such integer is realised.

## Main results

* `GilbertLattice.latticeSpectrum_eq_sums_of_two_squares` — the *spectrum* of the model
  (the set of squared edge lengths available to an aligned configuration) is exactly the
  set of positive sums of two squares;
* `GilbertLattice.prime_mem_latticeSpectrum_iff` — a prime `p` occurs as a squared edge
  length iff `p % 4 ≠ 3` (**Fermat's two-square theorem** read geometrically);
* `GilbertLattice.latticeSpectrum_iff_factorization` — the full arithmetic description:
  `n` occurs iff `n > 0` and every prime `q ≡ 3 [MOD 4]` divides `n` to an even power;
* `GilbertLattice.latticeSpectrum_mul` — the spectrum is closed under multiplication
  (Brahmagupta–Fibonacci: the geometry of the model is a *multiplicative monoid*);
* `GilbertLattice.exists_edge_of_length_sqrt_prime` — geometric form of the two-square
  theorem: for a prime `p` with `p % 4 ≠ 3` and any radius `R > √p`, the Gilbert graph
  of an aligned configuration contains an edge of length exactly `√p`, whereas for
  `p % 4 = 3` no edge of any aligned configuration has length `√p`;
* `GilbertLattice.alignedConfig_connected_iff` — an aligned configuration percolates (in
  fact is connected) exactly when `R > 1`, so `1` is the critical radius of the aligned
  subfamily, to be compared with `R_min ∈ [1/3, 1/2]` and `R_full = √5`;
* `GilbertLattice.neighborSet_alignedConfig` — for `1 < R ≤ √2` the neighbours of a cell
  are its four grid neighbours, the first instance of the Gauss circle problem.
-/

open GilbertLattice

/-! ## Aligned configurations -/


variable {s t : ℝ} {hs0 : 0 ≤ s} {hs1 : s ≤ 1} {ht0 : 0 ≤ t} {ht1 : t ≤ 1}

/-- In an aligned configuration the squared distance between two points is the squared
distance of the two cells: an integer of the form `a² + b²`. -/
lemma sqdist_alignedConfig (c c' : ℤ × ℤ) :
    sqdist (alignedConfig hs0 hs1 ht0 ht1) c c'
      = (((c.1 - c'.1) ^ 2 + (c.2 - c'.2) ^ 2 : ℤ) : ℝ) := by
  unfold sqdist px py alignedConfig
  push_cast
  ring



/-! ## The spectrum of squared edge lengths -/




/-- A sum of two squares is never `≡ 3 [MOD 4]`. -/
lemma sq_add_sq_mod_four_ne_three (x y : ℕ) : (x ^ 2 + y ^ 2) % 4 ≠ 3 := by
  have hx : x ^ 2 % 4 = (x % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
  have hy : y ^ 2 % 4 = (y % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
  have hadd : (x ^ 2 + y ^ 2) % 4 = (x ^ 2 % 4 + y ^ 2 % 4) % 4 := Nat.add_mod _ _ _
  have hx4 : x % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hy4 : y % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (x % 4) <;> interval_cases h2 : (y % 4) <;> omega

/-- **Fermat's two-square theorem, geometrically.**  A prime `p` is the squared length of
an edge of an aligned configuration if and only if `p % 4 ≠ 3`. -/
theorem prime_mem_latticeSpectrum_iff {p : ℕ} (hp : p.Prime) :
    p ∈ latticeSpectrum ↔ p % 4 ≠ 3 := by
  rw [latticeSpectrum_eq_sums_of_two_squares]
  constructor
  · rintro ⟨-, x, y, hxy⟩ h3
    exact sq_add_sq_mod_four_ne_three x y (hxy ▸ h3)
  · intro h3
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq h3
    exact ⟨hp.pos, a, b, hab.symm⟩





/-! ## Geometric consequences -/

/-- The distance between the points of two cells in an aligned configuration. -/
lemma pdist_alignedConfig (c c' : ℤ × ℤ) :
    pdist (alignedConfig hs0 hs1 ht0 ht1) c c'
      = Real.sqrt (((c.1 - c'.1) ^ 2 + (c.2 - c'.2) ^ 2 : ℤ) : ℝ) := by
  rw [pdist, sqdist_alignedConfig]



/-! ## The critical radius of the aligned subfamily -/





open GilbertLattice in
theorem solution{p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3)
    (c c' : ℤ × ℤ) (hne : c ≠ c') :
    pdist (alignedConfig hs0 hs1 ht0 ht1) c c' ≠ Real.sqrt p := by
  intro hcon
  rw [pdist_alignedConfig] at hcon
  have hnn : (0 : ℝ) ≤ (((c.1 - c'.1) ^ 2 + (c.2 - c'.2) ^ 2 : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ (c.1 - c'.1) ^ 2 + (c.2 - c'.2) ^ 2 := by positivity
    exact_mod_cast this
  have hpn : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have heq : (((c.1 - c'.1) ^ 2 + (c.2 - c'.2) ^ 2 : ℤ) : ℝ) = (p : ℝ) := by
    have h2 := congrArg (fun z : ℝ => z ^ 2) hcon
    simp only at h2
    rwa [Real.sq_sqrt hnn, Real.sq_sqrt hpn] at h2
  have hz : (c.1 - c'.1) ^ 2 + (c.2 - c'.2) ^ 2 = (p : ℤ) := by exact_mod_cast heq
  exact (prime_mem_latticeSpectrum_iff hp).1 ⟨c, c', hne, hz⟩ h3
