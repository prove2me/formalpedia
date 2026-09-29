-- Prove2me | solution 1 for Catalog.Geometry.Peel.body_peel_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:21:59.190471+00:00
-- url     : https://prove2.me/submissions/043aa5ca-0624-42cd-9408-27228f528696

-- Sol generated from Geometry/PeelDilationBodies.lean
import Mathlib
import Definitions.Def_Geometry_PeelDilationBodies
import Definitions.Def_Geometry_PeelStoppingTime
import Theorems.Thm_Catalog_Geometry_Peel_peel_extremal_tfae
/-
# Cycle 3: universality of the matching family

The shell peeling of a Euclidean ball saturates the peeling bound, and the
`O(d)`-action on its layers exhibits the symmetry responsible for that
saturation.  A natural criticism is that this could be an artefact of the
ball: the ball is the most symmetric body there is, so of course it produces a
symmetric peeling.

This file removes that objection: the construction is *universal*.  For **any**
star-shaped body `K ⊆ ℝ^d` of finite measure the dilates
`c_k • K`, `c_k = (1 - k/N)^{1/d}`, peel `K` into `N` pieces of equal measure
`vol K / N` (`bodyPeel_gap`, `bodyLayer_volume`), and every layer is invariant
under the *entire* linear symmetry group of `K` (`bodyLayer_equivariant`).
Conversely, a dilation peeling all of whose layers have measure at most
`vol K / N` must be this one (`body_peel_rigidity`).  The ball family of the
previous file is the special case `K = B(0,1)`, where the symmetry group is
`O(d)`.

The upshot for the original question — a matching family of actions for the
peeling upper bound — is that the extremisers are parameterised by *all* pairs
`(K, G)` with `G` a group of linear symmetries of `K`: the dimension `d` fixes
the radial profile `(1 - k/N)^{1/d}`, and the body `K` is otherwise free.

## Lab notes

Cross-check in `d = 2` with `K` the unit square `[-1,1]^2` (`vol K = 4`) and
`N = 4`: dilation factors `1, √(3)/2, √(2)/2, 1/2, 0`, layer areas
`4·(1/4) = 1` each — identical factors to the disc case, as the theory
predicts: the factors depend only on `d` and `N`, never on `K`.
-/

open Catalog.Geometry.Peel

open Finset MeasureTheory Metric Pointwise

/-! ## Volumes of dilates -/





/-! ## Star-shaped bodies and nested dilates -/



/-! ## The universal equal-volume dilation peeling -/


lemma dilationFactor_nonneg (d N k : ℕ) : 0 ≤ dilationFactor d N k :=
  Real.rpow_nonneg (le_max_left _ _) _


lemma dilationFactor_pow {d N k : ℕ} (hd : 0 < d) :
    (dilationFactor d N k) ^ d = max 0 (1 - (k : ℝ) / (N : ℝ)) :=
  Real.rpow_inv_natCast_pow (le_max_left _ _) hd.ne'










/-! ## Rigidity for arbitrary bodies -/





open Catalog.Geometry.Peel in
theorem solution(d N : ℕ) (hd : 0 < d) (hN : 0 < N)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hpos : 0 < bodyVol d K)
    (c : ℕ → ℝ) (hanti : Antitone c) (hnn : ∀ k, 0 ≤ c k) (h0 : c 0 = 1) (hlast : c N = 0)
    (hsmall : ∀ k < N, bodyVol d ((c k) • K) - bodyVol d ((c (k + 1)) • K) ≤ bodyVol d K / N) :
    ∀ k ≤ N, c k = dilationFactor d N k := by
  set P := dilationProfile d K c hanti hnn with hP
  have hsize : ∀ k, P.size k = bodyVol d ((c k) • K) := fun _ => rfl
  have hzero : bodyVol d ((c 0) • K) = bodyVol d K := by
    rw [h0]; simp [bodyVol]
  have hlast' : bodyVol d ((c N) • K) = 0 := by
    rw [hlast, bodyVol_smul (le_refl 0)]
    simp [hd.ne']
  have hbudget : peelBudget P N = bodyVol d K := by
    simp only [peelBudget, hsize, hzero, hlast', sub_zero]
  have hrate : peelRate P N = bodyVol d K / N := by rw [peelRate, hbudget]
  have h1 : ∀ k < N, peelGap P k ≤ peelRate P N := by
    intro k hk
    rw [hrate, peelGap, hsize, hsize]
    exact hsmall k hk
  have h3 := ((peel_extremal_tfae P hN).out 0 2).1 h1
  intro k hk
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hnneg : (0 : ℝ) ≤ 1 - (k : ℝ) / N := by
    rw [sub_nonneg, div_le_one hNR]; exact hkN
  -- the volume identity forces the `d`-th powers of the factors to agree
  have hvol : c k ^ d * bodyVol d K = (dilationFactor d N k) ^ d * bodyVol d K := by
    have hleft : bodyVol d ((c k) • K) = c k ^ d * bodyVol d K := bodyVol_smul (hnn k)
    have hstep := h3 k hk
    rw [hsize, hleft, hsize, hzero, hrate] at hstep
    rw [hstep, dilationFactor_pow hd, max_eq_right hnneg]
    field_simp
  have hpow : c k ^ d = (dilationFactor d N k) ^ d :=
    mul_right_cancel₀ hpos.ne' hvol
  rcases lt_trichotomy (c k) (dilationFactor d N k) with hlt | heq | hgt
  · have := pow_lt_pow_left₀ hlt (hnn k) hd.ne'; linarith
  · exact heq
  · have := pow_lt_pow_left₀ hgt (dilationFactor_nonneg d N k) hd.ne'; linarith
