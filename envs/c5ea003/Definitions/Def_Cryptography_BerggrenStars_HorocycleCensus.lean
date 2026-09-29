-- Prove2me | Definitions.Def_Cryptography_BerggrenStars_HorocycleCensus
-- name    : Cryptography_BerggrenStars_HorocycleCensus
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:12:12.068169+00:00
-- url     : https://prove2.me/theorems/3e760e64-7c0e-4c81-ac6c-a6d13b3ad38f
-- title:
--   Aether Catalog definitions — Cryptography_BerggrenStars_HorocycleCensus
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BerggrenStars.HorocycleCensus`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BerggrenStars/HorocycleCensus.lean by skeleton subtraction
import Mathlib
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

namespace BerggrenHypercycleStars

open Real UpperHalfPlane

/-- The Euclid seeds sitting on the horocycle `Im z = 1/m`, recorded by their second
coordinate. -/
def horocycleSeeds (m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun n => Nat.Coprime m n ∧ (m + n) % 2 = 1)






end BerggrenHypercycleStars


