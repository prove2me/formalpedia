-- Prove2me | Theorems.Thm_BerggrenHypercycleStars_exists_seed_slope_close
-- name    : BerggrenHypercycleStars.exists_seed_slope_close
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:34:26.893471+00:00
-- url     : https://prove2.me/theorems/a6533f7f-cab5-4ab0-a3a8-405c6f22b0ca
-- title:
--   Slopes of Euclid seeds are dense in `(0,1)`, with denominators as large as one likes.
-- statement:
--   **Slopes of Euclid seeds are dense in `(0,1)`**, with denominators as large as one likes.
--
--   ```lean
--   theorem BerggrenHypercycleStars.exists_seed_slope_close(t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (ε : ℝ) (hε : 0 < ε) :
--       ∃ m n : ℕ, IsSeed m n ∧ |(n : ℝ) / m - t| < ε ∧ 1 / (m : ℝ) < ε := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenStars/BoundaryLimitSet.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenStars/BoundaryLimitSet.lean#L41

-- Thm stub generated from Cryptography/BerggrenStars/BoundaryLimitSet.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars

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

theorem BerggrenHypercycleStars.exists_seed_slope_close(t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ m n : ℕ, IsSeed m n ∧ |(n : ℝ) / m - t| < ε ∧ 1 / (m : ℝ) < ε := by sorry
