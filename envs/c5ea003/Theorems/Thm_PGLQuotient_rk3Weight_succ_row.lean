-- Prove2me | Theorems.Thm_PGLQuotient_rk3Weight_succ_row
-- name    : PGLQuotient.rk3Weight_succ_row
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:48:55.332745+00:00
-- url     : https://prove2.me/theorems/e5c59b4d-4edf-490d-974e-368a49504177
-- title:
--   Rk3Weight succ row
-- statement:
--   Formal statement of `PGLQuotient.rk3Weight_succ_row` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem PGLQuotient.rk3Weight_succ_row(a b : ℕ) :
--       rk3Weight q (a + 1) b =
--         if b = 0 then (q ^ 5 * (q - 1) ^ 2 * (q ^ 2 - 1))⁻¹ * ((q ^ 2)⁻¹) ^ a
--         else ((q ^ 7 * (q - 1) ^ 3)⁻¹ * ((q ^ 2)⁻¹) ^ a) * ((q ^ 2)⁻¹) ^ (b - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PGLQuotient/VertexVolumeRankThree.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PGLQuotient/VertexVolumeRankThree.lean#L153

-- Thm stub generated from Algebra/PGLQuotient/VertexVolumeRankThree.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
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











/-! ### Summing over the dominant sector -/

theorem PGLQuotient.rk3Weight_succ_row(a b : ℕ) :
    rk3Weight q (a + 1) b =
      if b = 0 then (q ^ 5 * (q - 1) ^ 2 * (q ^ 2 - 1))⁻¹ * ((q ^ 2)⁻¹) ^ a
      else ((q ^ 7 * (q - 1) ^ 3)⁻¹ * ((q ^ 2)⁻¹) ^ a) * ((q ^ 2)⁻¹) ^ (b - 1) := by sorry
