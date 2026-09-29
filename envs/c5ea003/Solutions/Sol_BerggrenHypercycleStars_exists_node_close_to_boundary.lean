-- Prove2me | solution 1 for BerggrenHypercycleStars.exists_node_close_to_boundary
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:37:31.333599+00:00
-- url     : https://prove2.me/submissions/79c22562-fc5e-435c-95bd-971d570c9818

-- Sol generated from Cryptography/BerggrenStars/BoundaryLimitSet.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars
import Theorems.Thm_BerggrenHypercycleStars_exists_seed_slope_close

/-!
# Where the stars come from: the boundary limit set of the Berggren tree

The hypercycle stars of `Cryptography.BerggrenStars.HypercycleStars` sit over rational boundary
points. This file shows that the tree accumulates on *every* point of the boundary interval
`[0,1]`, so the visible rays are not an artifact of a few special cusps: the picture is a set of
curves radiating out of a dense set of boundary points.

The construction is completely explicit and uses only dyadic seeds: for `m = 2^j` every odd
`n < m` gives a Euclid seed (coprimality is automatic, opposite parity is automatic), and the
slopes `n / 2^j` with `n` odd are dense in `(0,1)`.

## Main results

* `isSeed_two_pow` : the dyadic seeds.
* `exists_seed_slope_close` : every `t ∈ (0,1)` is approximated to within `ε` by the slope `n/m`
  of a Euclid seed, with `1/m < ε` as well (the node is also close to the boundary).
* `exists_node_close_to_boundary` : every `t ∈ (0,1)` is a limit of Berggren nodes in `ℂ`; the
  limit set of the embedded tree contains the whole boundary interval.
-/

open BerggrenHypercycleStars

open Real UpperHalfPlane





open BerggrenHypercycleStars in
theorem solution(t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m n : ℕ) (hm : 0 < m), IsSeed m n ∧
      ‖((hpoint m n hm : ℍ) : ℂ) - (t : ℂ)‖ < ε := by
  obtain ⟨m, n, hseed, hclose, hheight⟩ :=
    exists_seed_slope_close t ht0 ht1 (ε / 2) (by linarith)
  have hm : 0 < m := lt_trans hseed.pos hseed.lt
  have hMR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  refine ⟨m, n, hm, hseed, ?_⟩
  have hre : (((hpoint m n hm : ℍ) : ℂ) - (t : ℂ)).re = (n : ℝ) / m - t := rfl
  have him : (((hpoint m n hm : ℍ) : ℂ) - (t : ℂ)).im = 1 / (m : ℝ) := by
    simp [hpoint]
  calc ‖((hpoint m n hm : ℍ) : ℂ) - (t : ℂ)‖
      ≤ |(((hpoint m n hm : ℍ) : ℂ) - (t : ℂ)).re|
        + |(((hpoint m n hm : ℍ) : ℂ) - (t : ℂ)).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |(n : ℝ) / m - t| + 1 / (m : ℝ) := by
        rw [hre, him, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (m : ℝ))]
    _ < ε := by linarith
