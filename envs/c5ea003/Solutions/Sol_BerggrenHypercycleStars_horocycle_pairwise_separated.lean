-- Prove2me | solution 1 for BerggrenHypercycleStars.horocycle_pairwise_separated
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:37:32.47241+00:00
-- url     : https://prove2.me/submissions/0074737d-d186-4018-9907-d08dd1fe15fb

-- Sol generated from Cryptography/BerggrenStars/HorocycleCensus.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HorocycleCensus
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars
import Theorems.Thm_BerggrenHypercycleStars_cosh_dist_same_height

/-!
# The curves of the Berggren picture: horocycle census

Besides the *stars* of hypercycles studied in `Cryptography.BerggrenStars.HypercycleStars`,
a picture of the Berggren tree embedded in the Poincaré half-plane by `z(m,n) = (n+i)/m` shows a
second family of curves: the **horizontal lines**, which are the horocycles based at the boundary
point `∞`. The nodes at height `1/m` are exactly the Euclid seeds with first coordinate `m`.

## Main results

* `card_horocycleSeeds_even`, `card_horocycleSeeds_odd` : an exact census of each horocycle.
  The horocycle at height `1/m` carries exactly `φ(m)` nodes when `m` is even, and exactly
  `φ(m)/2` nodes when `m` is odd — Euler's totient is the *occupation number* of the horocycle.
* `horocycleSeeds_nonempty` : every horocycle at height `1/m` with `m ≥ 2` is occupied.
* `horocycle_pairwise_separated` : the nodes on one horocycle are uniformly separated, at
  pairwise hyperbolic distance at least `arcosh (3/2)`, however deep in the tree they lie. So
  the horizontal curves of the picture are *uniformly discrete* point sets, in sharp contrast
  with the hypercycle rays, along which the nodes accumulate (`step_along_spoke_tendsto_zero`).
-/

open BerggrenHypercycleStars

open Real UpperHalfPlane








open BerggrenHypercycleStars in
theorem solution(m n n' : ℕ) (hm : 0 < m) (h : n ≠ n') :
    Real.arsinh (Real.sqrt 2 / 2) ≤ dist (hpoint m n hm) (hpoint m n' hm) := by
  have hkey : (3 : ℝ) / 2 ≤ Real.cosh (dist (hpoint m n hm) (hpoint m n' hm)) :=
    cosh_dist_same_height m n n' hm h
  have hc : Real.cosh (Real.arsinh (Real.sqrt 2 / 2)) = Real.sqrt (3 / 2) := by
    rw [Real.cosh_arsinh]
    congr 1
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hle : Real.cosh (Real.arsinh (Real.sqrt 2 / 2))
      ≤ Real.cosh (dist (hpoint m n hm) (hpoint m n' hm)) := by
    rw [hc]
    refine le_trans ?_ hkey
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h1 := Real.cosh_le_cosh.1 hle
  rwa [abs_of_nonneg (Real.arsinh_nonneg_iff.2 (by positivity)),
    abs_of_nonneg dist_nonneg] at h1
