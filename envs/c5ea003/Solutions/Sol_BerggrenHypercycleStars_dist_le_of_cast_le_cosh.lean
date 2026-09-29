-- Prove2me | solution 1 for BerggrenHypercycleStars.dist_le_of_cast_le_cosh
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:30:45.375351+00:00
-- url     : https://prove2.me/submissions/3305ad15-a546-4a70-bb36-e57d58df1891

-- Sol generated from Cryptography/BerggrenStars/RayDensity.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars
import Definitions.Def_Cryptography_BerggrenStars_RayDensity
import Theorems.Thm_BerggrenHypercycleStars_cosh_dist_hpoint_I

/-!
# How densely a single ray of the star is populated

`Cryptography.BerggrenStars.HypercycleStars` shows that the nodes with a fixed second Euclid
coordinate `n` all lie on one hypercycle (a Euclidean ray out of the boundary point `0`), and
that the hyperbolic steps along that ray tend to `0`. Here we count how many nodes of the ray
of index `n` lie inside the hyperbolic ball of radius `R` about `i`.

## Main results

* `dist_le_of_cast_le_cosh` : a very convenient membership test — *any* Euclid seed with
  `m ≤ cosh R` lies in the ball of radius `R`.
* `mem_rayNodes_iff` : the nodes of the ray of index `n` inside `B(R)` are exactly the seeds
  `(m, n)` with `m ≤ 2 cosh R` and `d ≤ R`; in particular there are finitely many.
* `card_rayNodes_le` : at most `2 cosh R` of them.
* `card_rayNodes_ge` : at least `(cosh R - (n+1))/(2n)` of them, obtained from the `B₃`-orbit of
  the left-spine seed `(n+1, n)`. So the linear density of nodes along the `n`-th ray decays
  like `1/(2n)`, while the total over all rays stays `Θ(e^{2R})`.
-/

open BerggrenHypercycleStars

open Real UpperHalfPlane









open BerggrenHypercycleStars in
theorem solution{m n : ℕ} (hseed : IsSeed m n) (R : ℝ) (hR : 0 ≤ R)
    (h : (m : ℝ) ≤ Real.cosh R) :
    dist (hpoint m n (lt_trans hseed.pos hseed.lt)) UpperHalfPlane.I ≤ R := by
  have hm : 0 < m := lt_trans hseed.pos hseed.lt
  have hMR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnm : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hseed.lt
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcosh : Real.cosh (dist (hpoint m n hm) UpperHalfPlane.I) ≤ Real.cosh R := by
    rw [cosh_dist_hpoint_I m n hm]
    refine le_trans ?_ h
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have := Real.cosh_le_cosh.1 hcosh
  rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg hR] at this
