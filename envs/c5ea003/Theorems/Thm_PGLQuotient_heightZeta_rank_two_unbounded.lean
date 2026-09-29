-- Prove2me | Theorems.Thm_PGLQuotient_heightZeta_rank_two_unbounded
-- name    : PGLQuotient.heightZeta_rank_two_unbounded
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:47:02.617981+00:00
-- url     : https://prove2.me/theorems/043f4fb9-c31d-4af7-ab99-dca5eacbeb19
-- title:
--   The pole at `s = d = 2` is genuine.
-- statement:
--   **The pole at `s = d = 2` is genuine.**  The rank-two height zeta function is unbounded
--   as `s ↑ 2`: for every `M` there is `s < 2` with `M < Z(s)`.  Together with
--   `summable_weight_height_iff` this pins the abscissa of convergence at exactly `s = 2`.
--
--   ```lean
--   theorem PGLQuotient.heightZeta_rank_two_unbounded(hq : 1 < q) (M : ℝ) :
--       ∃ s : ℝ, s < 2 ∧ M < heightZeta q 2 s := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PGLQuotient/HeightZetaRankTwo.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PGLQuotient/HeightZetaRankTwo.lean#L182

-- Thm stub generated from Algebra/PGLQuotient/HeightZetaRankTwo.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
import Definitions.Def_Algebra_PGLQuotient_HeightZetaRankTwo

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

open PGLQuotient

open Finset

variable {q : ℝ}

/-! ### Explicit rank-two data -/









/-! ### The height zeta function in rank two -/

theorem PGLQuotient.heightZeta_rank_two_unbounded(hq : 1 < q) (M : ℝ) :
    ∃ s : ℝ, s < 2 ∧ M < heightZeta q 2 s := by sorry
