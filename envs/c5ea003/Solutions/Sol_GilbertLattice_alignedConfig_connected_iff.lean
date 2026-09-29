-- Prove2me | solution 1 for GilbertLattice.alignedConfig_connected_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:30:09.170149+00:00
-- url     : https://prove2.me/submissions/28045454-f72c-42d5-aeaf-ffd6f04e1836

-- Sol generated from Shared/GilbertLatticeSumTwoSquares.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeSumTwoSquares
import Theorems.Thm_GilbertLattice_adj_alignedConfig_iff
import Theorems.Thm_GilbertLattice_connected_of_grid_adj
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

/-- In an aligned configuration the squared distance between two points is the squared
distance of the two cells: an integer of the form `a² + b²`. -/
lemma sqdist_alignedConfig (c c' : ℤ × ℤ) :
    sqdist (alignedConfig hs0 hs1 ht0 ht1) c c'
      = (((c.1 - c'.1) ^ 2 + (c.2 - c'.2) ^ 2 : ℤ) : ℝ) := by
  unfold sqdist px py alignedConfig
  push_cast
  ring



/-! ## The spectrum of squared edge lengths -/










/-! ## Geometric consequences -/




/-! ## The critical radius of the aligned subfamily -/

/-- Below radius `1` an aligned configuration has no edge at all. -/
lemma not_adj_alignedConfig_of_le_one {R : ℝ} (hR : R ≤ 1) (c c' : ℤ × ℤ) :
    ¬ (gilbert R (alignedConfig hs0 hs1 ht0 ht1)).Adj c c' := by
  rintro ⟨hne, hlt⟩
  have h1 : (1 : ℤ) ≤ (c.1 - c'.1) ^ 2 + (c.2 - c'.2) ^ 2 := one_le_cell_sqdist hne
  have h1' : (1 : ℝ) ≤ sqdist (alignedConfig hs0 hs1 ht0 ht1) c c' := by
    rw [sqdist_alignedConfig]; exact_mod_cast h1
  have : (1 : ℝ) ≤ pdist (alignedConfig hs0 hs1 ht0 ht1) c c' := by
    rw [pdist, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt h1'
  linarith




open GilbertLattice in
theorem solution{R : ℝ} :
    (gilbert R (alignedConfig hs0 hs1 ht0 ht1)).Connected ↔ 1 < R := by
  constructor
  · intro hconn
    by_contra hcon
    push_neg at hcon
    obtain ⟨w⟩ := hconn.preconnected (0, 0) (1, 0)
    cases w with
    | cons hadj w' => exact not_adj_alignedConfig_of_le_one hcon _ _ hadj
  · intro hR
    have hR0 : (0 : ℝ) < R := by linarith
    refine connected_of_grid_adj (fun i j => ?_) (fun i j => ?_)
    · refine (adj_alignedConfig_iff hR0 _ _).2 ⟨by intro h; rw [Prod.ext_iff] at h; omega, ?_⟩
      have : ((i : ℤ) - (i + 1)) ^ 2 + ((j : ℤ) - j) ^ 2 = 1 := by ring
      simp only [this]
      push_cast
      nlinarith
    · refine (adj_alignedConfig_iff hR0 _ _).2 ⟨by intro h; rw [Prod.ext_iff] at h; omega, ?_⟩
      have : ((i : ℤ) - i) ^ 2 + ((j : ℤ) - (j + 1)) ^ 2 = 1 := by ring
      simp only [this]
      push_cast
      nlinarith
