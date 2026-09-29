-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.cosh_dist_hpoint_I
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T01:44:10.267003+00:00
-- url     : https://prove2.me/submissions/ed2d4769-35d2-4f67-a52f-a52911c34b4a

/-
# `HyperbolicBerggrenGeodesics.cosh_dist_hpoint_I`
Target `073c9395` (Open, not deprecated at submission time).

Reduction to the Proved platform node `BerggrenHypercycleStars.cosh_dist_hpoint_I`. The two
namespaces declare byte-identical copies of `hpoint`, so they are distinct constants naming the
same point of the upper half-plane. The bridge identifies them; it is restated inline because a
submission may never import another `Solutions` module.
-/
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Theorems.Thm_BerggrenHypercycleStars_cosh_dist_hpoint_I

set_option autoImplicit false

namespace DupBridge

theorem hpoint_eq (m n : ℕ) (hm : 0 < m) :
    HyperbolicBerggrenGeodesics.hpoint m n hm = BerggrenHypercycleStars.hpoint m n hm := by
  first
  | rfl
  | · apply Subtype.ext
      simp [HyperbolicBerggrenGeodesics.hpoint, BerggrenHypercycleStars.hpoint]

end DupBridge

open HyperbolicBerggrenGeodesics in
/-- **The target, verbatim.** Reduction to the Proved Berggren-stars node. -/
theorem solution (m n : ℕ) (hm : 0 < m) :
    Real.cosh (dist (hpoint m n hm) UpperHalfPlane.I)
      = ((m : ℝ) ^ 2 + (n : ℝ) ^ 2 + 1) / (2 * m) := by
  first
  | exact BerggrenHypercycleStars.cosh_dist_hpoint_I m n hm
  | · rw [DupBridge.hpoint_eq]
      exact BerggrenHypercycleStars.cosh_dist_hpoint_I m n hm
