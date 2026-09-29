-- Prove2me | Theorems.Thm_BerggrenHypercycleStars_mem_horocycleSeeds_iff
-- name    : BerggrenHypercycleStars.mem_horocycleSeeds_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:34:35.342426+00:00
-- url     : https://prove2.me/theorems/b8b9b4cc-c736-4103-94f0-92e71dc0f2c6
-- title:
--   Mem horocycleSeeds iff
-- statement:
--   Formal statement of `BerggrenHypercycleStars.mem_horocycleSeeds_iff` from the Aether Catalog (Cryptography). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem BerggrenHypercycleStars.mem_horocycleSeeds_iff(m n : ℕ) (hm : 2 ≤ m) :
--       n ∈ horocycleSeeds m ↔ IsSeed m n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenStars/HorocycleCensus.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenStars/HorocycleCensus.lean#L32

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

theorem BerggrenHypercycleStars.mem_horocycleSeeds_iff(m n : ℕ) (hm : 2 ≤ m) :
    n ∈ horocycleSeeds m ↔ IsSeed m n := by sorry
