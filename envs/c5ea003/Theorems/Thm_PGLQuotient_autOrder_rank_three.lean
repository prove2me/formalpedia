-- Prove2me | Theorems.Thm_PGLQuotient_autOrder_rank_three
-- name    : PGLQuotient.autOrder_rank_three
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:44:26.254923+00:00
-- url     : https://prove2.me/theorems/e9b65a1d-d456-40ee-a46b-321f6f80a286
-- title:
--   The exact stabiliser order in rank three, in the four strata of the dominant sector.
-- statement:
--   **The exact stabiliser order in rank three**, in the four strata of the dominant sector.
--
--   ```lean
--   theorem PGLQuotient.autOrder_rank_three(hq : 1 < q) (g : Vertex 3) :
--       autOrder q g =
--         if g 0 = 0 then
--           (if g 1 = 0 then q ^ 3 * (q - 1) * (q ^ 2 - 1) * (q ^ 3 - 1)
--            else q ^ (2 * g 1 + 3) * (q - 1) ^ 2 * (q ^ 2 - 1))
--         else
--           (if g 1 = 0 then q ^ (2 * g 0 + 3) * (q - 1) ^ 2 * (q ^ 2 - 1)
--            else q ^ (2 * g 0 + 2 * g 1 + 3) * (q - 1) ^ 3) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PGLQuotient/VertexVolumeRankThree.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PGLQuotient/VertexVolumeRankThree.lean#L93

-- Thm stub generated from Algebra/PGLQuotient/VertexVolumeRankThree.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Definitions.Def_Algebra_PGLQuotient_VertexVolumeRankThree

/-!
# Rank three: the exact vertex volume in closed product form

We evaluate, with no sorries, the total vertex mass of the standard arithmetic quotient
of the affine Bruhat–Tits building of `PGL_3(F_q((t^{-1})))`:

`∑_λ 1/|Aut λ| = 3 / ((q-1)^2 (q^2-1)^2 (q^3-1)) = 3 / (P(3) P(2))`,

where `P(m) = ∏_{k=1}^m (q^k - 1)`.  Equivalently the `PGL`-normalised vertex volume is
`(q-1) ∑_λ 1/|Aut λ| = 3/((q-1)(q^2-1)^2(q^3-1))`.

This is the `d = 3` instance of the conjectured closed product form
`d (q-1) / (P(d) P(d-1))` (see `FUTURE_DIRECTIONS.md`); the `d = 2` instance is
`vertexVolume_rank_two`.

The proof is the building-theoretic one: vertices are parametrised by the dominant sector
(here `ℕ^2` in gap coordinates), the stabiliser orders are computed *exactly* in the four
strata `g = (0,0)`, `(0,b)`, `(a,0)`, `(a,b)` cut out by the vanishing of the gaps, and the
resulting sum over the strata (the `d = 3` "cut-set" decomposition) is summed as a double
geometric series.
-/

open PGLQuotient

open Finset

variable {q : ℝ}

/-! ### A geometric summation helper -/



/-! ### Explicit rank-three data -/

theorem PGLQuotient.autOrder_rank_three(hq : 1 < q) (g : Vertex 3) :
    autOrder q g =
      if g 0 = 0 then
        (if g 1 = 0 then q ^ 3 * (q - 1) * (q ^ 2 - 1) * (q ^ 3 - 1)
         else q ^ (2 * g 1 + 3) * (q - 1) ^ 2 * (q ^ 2 - 1))
      else
        (if g 1 = 0 then q ^ (2 * g 0 + 3) * (q - 1) ^ 2 * (q ^ 2 - 1)
         else q ^ (2 * g 0 + 2 * g 1 + 3) * (q - 1) ^ 3) := by sorry
