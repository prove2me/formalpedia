-- Prove2me | Theorems.Thm_BerggrenHypercycleStars_horocycle_pairwise_separated
-- name    : BerggrenHypercycleStars.horocycle_pairwise_separated
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:34:16.045259+00:00
-- url     : https://prove2.me/theorems/5175fc69-c612-4097-8229-bfd1ebc2d790
-- title:
--   The horizontal curves are uniformly discrete.
-- statement:
--   **The horizontal curves are uniformly discrete.** Any two distinct nodes on one horocycle
--   are at hyperbolic distance at least `arcosh (3/2) = 0.9624…`, uniformly in `m`; contrast with
--   the hypercycle rays of the stars, along which the hyperbolic steps tend to `0`.
--
--   ```lean
--   theorem BerggrenHypercycleStars.horocycle_pairwise_separated(m n n' : ℕ) (hm : 0 < m) (h : n ≠ n') :
--       Real.arsinh (Real.sqrt 2 / 2) ≤ dist (hpoint m n hm) (hpoint m n' hm) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenStars/HorocycleCensus.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenStars/HorocycleCensus.lean#L131

-- Thm stub generated from Cryptography/BerggrenStars/HorocycleCensus.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HorocycleCensus
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars

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

theorem BerggrenHypercycleStars.horocycle_pairwise_separated(m n n' : ℕ) (hm : 0 < m) (h : n ≠ n') :
    Real.arsinh (Real.sqrt 2 / 2) ≤ dist (hpoint m n hm) (hpoint m n' hm) := by sorry
