-- Prove2me | solution 1 for GilbertLattice.neighborSet_alignedConfig
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:36:27.199304+00:00
-- url     : https://prove2.me/submissions/60539353-ef13-45cd-b034-ebcac9ae3395

-- Sol generated from Shared/GilbertLatticeSumTwoSquares.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeSumTwoSquares
import Theorems.Thm_GilbertLattice_adj_alignedConfig_iff
import Theorems.Thm_GilbertLattice_one_le_cell_sqdist

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




/-! ## The spectrum of squared edge lengths -/










/-! ## Geometric consequences -/




/-! ## The critical radius of the aligned subfamily -/





open GilbertLattice in
theorem solution{R : ℝ} (hR : 1 < R) (hR2 : R ≤ Real.sqrt 2) (c : ℤ × ℤ) :
    (gilbert R (alignedConfig hs0 hs1 ht0 ht1)).neighborSet c
      = {(c.1 + 1, c.2), (c.1 - 1, c.2), (c.1, c.2 + 1), (c.1, c.2 - 1)} := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hRsq : R ^ 2 ≤ 2 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  ext c'
  simp only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [adj_alignedConfig_iff hR0]
  constructor
  · rintro ⟨hne, hlt⟩
    have h1 : (1 : ℤ) ≤ (c.1 - c'.1) ^ 2 + (c.2 - c'.2) ^ 2 := one_le_cell_sqdist hne
    have h2 : (((c.1 - c'.1) ^ 2 + (c.2 - c'.2) ^ 2 : ℤ) : ℝ) < 2 := lt_of_lt_of_le hlt hRsq
    have h2' : (c.1 - c'.1) ^ 2 + (c.2 - c'.2) ^ 2 < 2 := by exact_mod_cast h2
    have heq : (c.1 - c'.1) ^ 2 + (c.2 - c'.2) ^ 2 = 1 := by omega
    have hx : (c.1 - c'.1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (c.2 - c'.2)]
    have hy : (c.2 - c'.2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (c.1 - c'.1)]
    have hxb : -1 ≤ c.1 - c'.1 ∧ c.1 - c'.1 ≤ 1 := by constructor <;> nlinarith
    have hyb : -1 ≤ c.2 - c'.2 ∧ c.2 - c'.2 ≤ 1 := by constructor <;> nlinarith
    have hx1 : c.1 - c'.1 = -1 ∨ c.1 - c'.1 = 0 ∨ c.1 - c'.1 = 1 := by omega
    have hy1 : c.2 - c'.2 = -1 ∨ c.2 - c'.2 = 0 ∨ c.2 - c'.2 = 1 := by omega
    rcases hx1 with h | h | h <;> rcases hy1 with h' | h' | h' <;>
      rw [h, h'] at heq <;> norm_num at heq <;> simp only [Prod.ext_iff] <;> omega
  · intro h
    have hxy : (c.1 - c'.1) ^ 2 + (c.2 - c'.2) ^ 2 = 1 := by
      rcases h with h | h | h | h <;> rw [h] <;> simp
    refine ⟨?_, ?_⟩
    · intro hc
      rw [hc] at hxy
      simp at hxy
    · rw [hxy]
      push_cast
      nlinarith
