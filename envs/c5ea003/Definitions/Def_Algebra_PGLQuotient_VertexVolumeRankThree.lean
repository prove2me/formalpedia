-- Prove2me | Definitions.Def_Algebra_PGLQuotient_VertexVolumeRankThree
-- name    : Algebra_PGLQuotient_VertexVolumeRankThree
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:33:12.641197+00:00
-- url     : https://prove2.me/theorems/7b814701-05d2-4aa7-924d-3eb9d60d54cf
-- title:
--   Aether Catalog definitions — Algebra_PGLQuotient_VertexVolumeRankThree
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PGLQuotient.VertexVolumeRankThree`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PGLQuotient/VertexVolumeRankThree.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail

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

namespace PGLQuotient

open Finset

variable {q : ℝ}

/-! ### A geometric summation helper -/



/-! ### Explicit rank-three data -/









/-- The vertex mass in rank three, in the four strata. -/
noncomputable def rk3Weight (q : ℝ) (a b : ℕ) : ℝ :=
  if a = 0 then
    (if b = 0 then (q ^ 3 * (q - 1) * (q ^ 2 - 1) * (q ^ 3 - 1))⁻¹
     else (q ^ (2 * b + 3) * (q - 1) ^ 2 * (q ^ 2 - 1))⁻¹)
  else
    (if b = 0 then (q ^ (2 * a + 3) * (q - 1) ^ 2 * (q ^ 2 - 1))⁻¹
     else (q ^ (2 * a + 2 * b + 3) * (q - 1) ^ 3)⁻¹)


/-! ### Summing over the dominant sector -/





end PGLQuotient


