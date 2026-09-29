-- Prove2me | Theorems.Thm_BerggrenHypercycleStars_dist_le_of_cast_le_cosh
-- name    : BerggrenHypercycleStars.dist_le_of_cast_le_cosh
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:33:49.715086+00:00
-- url     : https://prove2.me/theorems/cd51924f-3c03-4fdf-82a2-8297807912c8
-- title:
--   Ball membership test.
-- statement:
--   **Ball membership test.** Every Euclid seed whose first coordinate is at most `cosh R` gives
--   a node inside the hyperbolic ball of radius `R` about `i`.
--
--   ```lean
--   theorem BerggrenHypercycleStars.dist_le_of_cast_le_cosh{m n : ℕ} (hseed : IsSeed m n) (R : ℝ) (hR : 0 ≤ R)
--       (h : (m : ℝ) ≤ Real.cosh R) :
--       dist (hpoint m n (lt_trans hseed.pos hseed.lt)) UpperHalfPlane.I ≤ R := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenStars/RayDensity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenStars/RayDensity.lean#L27

-- Thm stub generated from Cryptography/BerggrenStars/RayDensity.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars
import Definitions.Def_Cryptography_BerggrenStars_RayDensity

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

theorem BerggrenHypercycleStars.dist_le_of_cast_le_cosh{m n : ℕ} (hseed : IsSeed m n) (R : ℝ) (hR : 0 ≤ R)
    (h : (m : ℝ) ≤ Real.cosh R) :
    dist (hpoint m n (lt_trans hseed.pos hseed.lt)) UpperHalfPlane.I ≤ R := by sorry
