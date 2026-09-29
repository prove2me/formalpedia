-- Prove2me | Theorems.Thm_PGLQuotient_prod_gapRatioW
-- name    : PGLQuotient.prod_gapRatioW
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:47:38.499559+00:00
-- url     : https://prove2.me/theorems/2de18a3d-a1a0-4abc-94bf-89c16b3b7725
-- title:
--   Prod gapRatioW
-- statement:
--   Formal statement of `PGLQuotient.prod_gapRatioW` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem PGLQuotient.prod_gapRatioW(w : ℝ) (g : Vertex d) :
--       ∏ k, gapRatioW q d w k ^ g k = (q ^ pairExp g)⁻¹ * w ^ heightExp g := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PGLQuotient/HeightZetaGeneral.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PGLQuotient/HeightZetaGeneral.lean#L55

-- Thm stub generated from Algebra/PGLQuotient/HeightZetaGeneral.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightZetaGeneral
import Definitions.Def_Algebra_PGLQuotient_HeightZetaRankTwo
import Definitions.Def_Algebra_PGLQuotient_VertexModel

/-!
# The height zeta function in arbitrary rank: rationality and the pole at `s = d`

`Algebra.PGLQuotient.HeightZetaRankTwo` computes the positive-moment height zeta function

`Z_d(s) = ∑_λ α(λ)^s / |Aut λ|`

of the standard arithmetic quotient of `PGL_d(F_q((t^{-1})))` in closed form for `d = 2`,
exhibiting it as a rational function of `u = q^{s/2}` with a single pole at `u = q`.
This file establishes the corresponding statement in **arbitrary rank `d ≥ 1`**.

The mechanism is the same row-peeling recursion that produced the vertex volume in
`Algebra.PGLQuotient.VertexVolumeGeneral`, run on a *height-weighted* twisted mass

`twZ q c j w λ = w ^ heightExp λ · twWeight q c j λ`.

Since `heightExp (cons a λ') = (n+1)·a + heightExp λ'`, the extra factor is compatible with
peeling: it only changes the ratio of the geometric series in the top gap from
`q^{-(n+1)(c+1)}` to `w^{n+1} q^{-(n+1)(c+1)}`.  Hence:

* `twZMass_succ` — the row-peeling recursion for the height-weighted twisted mass;
* `twZ_rational` — for every rank and every pair of twisting parameters the sum is a rational
  function of `w` on the whole interval `0 ≤ w < q`, with a denominator that does not vanish
  there;
* `heightZeta_rational_general` — **the height zeta function of the rank-`d` quotient is a
  rational function of `u = q^{s/d}`**, uniformly for `s < d`;
* `heightZeta_unbounded_general` — **the pole at `s = d` is genuine in every rank**:
  `Z_d(s) → ∞` as `s ↑ d`.  Combined with `summable_weight_height_iff` this pins the abscissa
  of convergence at exactly `s = d`.

The threshold `w < q` is exactly `s < d` under `w = q^{s/d}`, so the domain of rationality is
precisely the half-plane of convergence.
-/

open PGLQuotient

open Finset

variable {q : ℝ}




variable {d : ℕ}

theorem PGLQuotient.prod_gapRatioW(w : ℝ) (g : Vertex d) :
    ∏ k, gapRatioW q d w k ^ g k = (q ^ pairExp g)⁻¹ * w ^ heightExp g := by sorry
