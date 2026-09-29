-- Prove2me | Definitions.Def_Cryptography_BerggrenStars_RayDensity
-- name    : Cryptography_BerggrenStars_RayDensity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:12:31.597969+00:00
-- url     : https://prove2.me/theorems/6ad66eaa-9b81-4136-9bcc-47e7b8f0f57f
-- title:
--   Aether Catalog definitions — Cryptography_BerggrenStars_RayDensity
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BerggrenStars.RayDensity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BerggrenStars/RayDensity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars

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

namespace BerggrenHypercycleStars

open Real UpperHalfPlane



open Classical in
/-- The nodes of the ray of index `n` (the `n`-th hypercycle of the `0`-star) inside the
hyperbolic ball of radius `R`, recorded by their first Euclid coordinate. -/
noncomputable def rayNodes (n : ℕ) (R : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊2 * Real.cosh R⌋₊).filter
    (fun m => ∃ hm : 0 < m, IsSeed m n ∧ dist (hpoint m n hm) UpperHalfPlane.I ≤ R)





end BerggrenHypercycleStars


