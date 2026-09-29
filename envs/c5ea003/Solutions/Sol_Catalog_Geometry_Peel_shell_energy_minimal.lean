-- Prove2me | solution 1 for Catalog.Geometry.Peel.shell_energy_minimal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:35:51.958071+00:00
-- url     : https://prove2.me/submissions/820ef757-450f-4799-a154-9d26a3d680f3

-- Sol generated from Geometry/PeelEnergyVariational.lean
import Mathlib
import Definitions.Def_Geometry_PeelDilationBodies
import Definitions.Def_Geometry_PeelEnergyVariational
import Definitions.Def_Geometry_PeelStoppingTime
import Definitions.Def_Geometry_PeelSymmetryConstruction
import Theorems.Thm_Catalog_Geometry_Peel_ballVol_zero
import Theorems.Thm_Catalog_Geometry_Peel_peel_energy_identity
import Theorems.Thm_Catalog_Geometry_Peel_shellPeel_gap
import Theorems.Thm_Catalog_Geometry_Peel_shellPeel_size
/-
# Cycle 4: the variational characterisation of extremal peelings

Cycles 1–3 characterise the extremisers of the peeling bound by an
*inequality* (all layers small), by a *symmetry* (invariance of the layer
contents under a transitive action) and by an explicit *geometric family*
(equal-measure dilations of a star-shaped body).  This file adds the fourth,
variational, description and ties it to the previous three.

Write `A = peelBudget P N` for the content removed in a window of `N` steps.
The **layer energy** of the window is `∑_{k<N} gap_k²`.  The exact identity

`∑_{k<N} gap_k² - A²/N = ∑_{k<N} (gap_k - A/N)²`   (`peel_energy_identity`)

immediately gives:

* `peel_energy_ge` — the energy is at least `A²/N` (a Cauchy–Schwarz bound
  obtained here by a square-completion, with no appeal to Cauchy–Schwarz);
* `peel_energy_eq_iff_extremal` — equality holds exactly for the extremisers
  of the stopping-time bound, giving a second, independent proof of the
  rigidity theorem `peel_extremal_tfae`;
* `exists_peel_large_gap` — the dual pigeonhole: every window also contains a
  step whose layer is at least the average, so `min gap ≤ rate ≤ max gap`
  with a double equality precisely in the extremal case.

The geometric corollary `shell_energy_minimal` states that among all ball
peelings of `B(0,R) ⊆ ℝ^d` into `N` shells, the equal-volume shells of
`shellRadius` minimise the sum of squared shell volumes.

## Lab notes

`N = 4`, `A = 1`.  Uniform gaps `(¼,¼,¼,¼)`: energy `4·1/16 = 0.25 = A²/N`.
Front-loaded gaps `(1,0,0,0)`: energy `1`, excess `0.75`, which equals
`∑ (gap - ¼)² = (3/4)² + 3·(1/4)² = 0.5625 + 0.1875 = 0.75` — the identity
checks out numerically, and the excess is exactly the variance of the layer
distribution.
-/

open Catalog.Geometry.Peel

open Finset MeasureTheory

variable (P : PeelProfile) {N : ℕ}

/-! ## The energy identity -/



/-- **The energy is minimised by the extremal peelings.**  Every window of `N`
steps has layer energy at least `A²/N`. -/
theorem peel_energy_ge (hN : 0 < N) :
    (peelBudget P N) ^ 2 / N ≤ peelEnergy P N := by
  have h := peel_energy_identity P hN
  have hnn : 0 ≤ ∑ k ∈ range N, (peelGap P k - peelRate P N) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  linarith


/-! ## The dual pigeonhole -/



/-! ## Geometric corollary: equal-volume shells minimise the shell energy -/



open Catalog.Geometry.Peel in
theorem solution(d N : ℕ) (hd : 0 < d) (hN : 0 < N) {R : ℝ} (hR : 0 ≤ R)
    (r : ℕ → ℝ) (hanti : Antitone r) (hnn : ∀ k, 0 ≤ r k) (h0 : r 0 = R) (hlast : r N = 0) :
    (ballVol d R) ^ 2 / N
      ≤ ∑ k ∈ range N, (ballVol d (r k) - ballVol d (r (k + 1))) ^ 2 ∧
    ∑ k ∈ range N,
        (ballVol d (shellRadius R d N k) - ballVol d (shellRadius R d N (k + 1))) ^ 2
      = (ballVol d R) ^ 2 / N := by
  set P := radiusProfile d hd r hanti hnn with hP
  have hsize : ∀ j, P.size j = ballVol d (r j) := fun _ => rfl
  have hbudget : peelBudget P N = ballVol d R := by simp [peelBudget, hsize, h0, hlast]
  constructor
  · have h := peel_energy_ge P hN
    rw [hbudget] at h
    simpa [peelEnergy, peelGap, hsize] using h
  · have hgap : ∀ k ∈ range N,
        (ballVol d (shellRadius R d N k) - ballVol d (shellRadius R d N (k + 1))) ^ 2
          = (ballVol d R / N) ^ 2 := by
      intro k hk
      have hk' : k < N := Finset.mem_range.1 hk
      have := shellPeel_gap d N k hN hk' (R := R)
      rw [← shellPeel_size d N k hd hR, ← shellPeel_size d N (k + 1) hd hR]
      rw [show (shellPeel d R N).size k - (shellPeel d R N).size (k + 1)
        = peelGap (shellPeel d R N) k from rfl, this]
    rw [Finset.sum_congr rfl hgap, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    field_simp
