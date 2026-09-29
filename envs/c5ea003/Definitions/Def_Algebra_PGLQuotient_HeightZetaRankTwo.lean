-- Prove2me | Definitions.Def_Algebra_PGLQuotient_HeightZetaRankTwo
-- name    : Algebra_PGLQuotient_HeightZetaRankTwo
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:30:04.738448+00:00
-- url     : https://prove2.me/theorems/e9cbde97-0c59-417b-9577-502861650db7
-- title:
--   Aether Catalog definitions — Algebra_PGLQuotient_HeightZetaRankTwo
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PGLQuotient.HeightZetaRankTwo`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PGLQuotient/HeightZetaRankTwo.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
import Definitions.Def_Algebra_PGLQuotient_VertexModel

/-!
# Rank two: exact vertex volume and the height zeta function

For `d = 2` the standard arithmetic quotient is the ray `Γ \ X` of Serre's theory of trees:
the vertex `λ = (n, 0)` has stabiliser of order `|GL_2(F_q)|` for `n = 0` and
`(q-1)^2 q^{n+1}` for `n ≥ 1`.  We compute here, with no sorries:

* `autOrder_rank_two` : the exact stabiliser order;
* `heightZeta_rank_two` : the positive-moment height zeta function
  `Z(s) = ∑_λ α(λ)^s / |Aut λ|` in closed form for `s < 2`, exhibiting it as a *rational*
  function of `u = q^{s/2}`, namely
  `Z = 1/(q(q-1)(q^2-1)) + u/((q-1)^2 q (q-u))`,
  whose unique pole sits at `u = q`, i.e. exactly at `s = d = 2`;
* `vertexMass_rank_two`, `vertexVolume_rank_two` : the closed product form of the vertex
  volume, obtained by specialising to `s = 0`:
  `∑_λ 1/|Aut λ| = 2/((q-1)^2 (q^2-1))`, so the `PGL`-normalised vertex volume is
  `(q-1) ∑_λ 1/|Aut λ| = 2/((q-1)(q^2-1))`;
* `heightZeta_rank_two_unbounded` : `Z(s) → ∞` as `s ↑ 2`, i.e. the pole is genuine.
-/

namespace PGLQuotient

open Finset

variable {q : ℝ}

/-! ### Explicit rank-two data -/









/-! ### The height zeta function in rank two -/

/-- The positive-moment height zeta function of the quotient (Mellin transform of the
cusp-height distribution). -/
noncomputable def heightZeta (q : ℝ) (d : ℕ) (s : ℝ) : ℝ :=
  ∑' g : Vertex d, vertexWeight q g * height q g ^ s






end PGLQuotient


