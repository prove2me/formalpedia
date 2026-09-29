-- Prove2me | Theorems.Thm_BerggrenHypercycleStars_card_rayNodes_ge
-- name    : BerggrenHypercycleStars.card_rayNodes_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:33:37.832205+00:00
-- url     : https://prove2.me/theorems/69e9fee7-9f72-44db-9c23-6f046cbdc416
-- title:
--   Lower bound on the population of one ray.
-- statement:
--   **Lower bound on the population of one ray.** The ray of index `n` carries at least
--   `(cosh R - (n+1)) / (2n)` nodes inside the ball of radius `R`: the linear density along the
--   `n`-th ray decays like `1/(2n)`.
--
--   ```lean
--   theorem BerggrenHypercycleStars.card_rayNodes_ge(n : ℕ) (hn : 0 < n) (R : ℝ) (hR : 0 ≤ R)
--       (hcosh : (n : ℝ) + 1 ≤ Real.cosh R) :
--       (Real.cosh R - ((n : ℝ) + 1)) / (2 * n) ≤ (rayNodes n R).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenStars/RayDensity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenStars/RayDensity.lean#L99

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

theorem BerggrenHypercycleStars.card_rayNodes_ge(n : ℕ) (hn : 0 < n) (R : ℝ) (hR : 0 ≤ R)
    (hcosh : (n : ℝ) + 1 ≤ Real.cosh R) :
    (Real.cosh R - ((n : ℝ) + 1)) / (2 * n) ≤ (rayNodes n R).card := by sorry
