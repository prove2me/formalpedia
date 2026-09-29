-- Prove2me | Definitions.Def_Algebra_PGLQuotient_HeightZetaGeneral
-- name    : Algebra_PGLQuotient_HeightZetaGeneral
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:33:04.904656+00:00
-- url     : https://prove2.me/theorems/d35e0820-323f-418e-a210-2dbc4c3de075
-- title:
--   Aether Catalog definitions — Algebra_PGLQuotient_HeightZetaGeneral
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PGLQuotient.HeightZetaGeneral`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PGLQuotient/HeightZetaGeneral.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightZetaRankTwo
import Definitions.Def_Algebra_PGLQuotient_TwistedWeight
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

namespace PGLQuotient

open Finset

variable {q : ℝ}

/-- The height-weighted twisted vertex mass: `w^{heightExp λ} · twWeight q c j λ`. -/
noncomputable def twZ {d : ℕ} (q : ℝ) (c j : ℕ) (w : ℝ) (g : Vertex d) : ℝ :=
  w ^ heightExp g * twWeight q c j g

section Summability

/-- The base of the geometric series in the `k`-th gap direction, with height weight `w`. -/
noncomputable def gapRatioW (q : ℝ) (d : ℕ) (w : ℝ) (k : Fin (d - 1)) : ℝ :=
  (q ^ (((k : ℕ) + 1) * (d - 1 - (k : ℕ))))⁻¹ * w ^ (d - 1 - (k : ℕ))

variable {d : ℕ}




end Summability

section Recursion


variable {w : ℝ}





end Recursion

section Rationality

open Polynomial



end Rationality

section Pole


end Pole

end PGLQuotient


