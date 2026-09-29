-- Prove2me | solution 1 for GilbertLattice.latticeSpectrum_eq_gaussianInt_norms
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:36:25.552687+00:00
-- url     : https://prove2.me/submissions/6a8c1fe8-0725-4fcf-ad72-862169638260

-- Sol generated from Shared/GilbertLatticeSumTwoSquares.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeSumTwoSquares
import Theorems.Thm_GilbertLattice_mem_latticeSpectrum_iff

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
theorem solution:
    latticeSpectrum = {n : ℕ | ∃ z : GaussianInt, z ≠ 0 ∧ Zsqrtd.norm z = (n : ℤ)} := by
  ext n
  rw [mem_latticeSpectrum_iff]
  constructor
  · rintro ⟨hpos, a, b, hab⟩
    refine ⟨⟨a, b⟩, ?_, ?_⟩
    · intro hz
      rw [Zsqrtd.ext_iff] at hz
      simp only [Zsqrtd.re_zero, Zsqrtd.im_zero] at hz
      rw [hz.1, hz.2] at hab
      norm_num at hab
      omega
    · rw [Zsqrtd.norm_def]
      simp only
      linarith [hab, sq_nonneg a]
  · rintro ⟨z, hz, hnorm⟩
    have hzz : z.re ^ 2 + z.im ^ 2 = (n : ℤ) := by
      rw [Zsqrtd.norm_def] at hnorm
      nlinarith [hnorm]
    refine ⟨?_, z.re, z.im, hzz⟩
    have hne : z.re ≠ 0 ∨ z.im ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hz (Zsqrtd.ext_iff.2 ⟨by simpa using hcon.1, by simpa using hcon.2⟩)
    have hposz : 0 < z.re ^ 2 + z.im ^ 2 := by
      rcases hne with h | h
      · have : 0 < z.re ^ 2 := by positivity
        nlinarith [sq_nonneg z.im]
      · have : 0 < z.im ^ 2 := by positivity
        nlinarith [sq_nonneg z.re]
    have : (0 : ℤ) < (n : ℤ) := hzz ▸ hposz
    exact_mod_cast this
