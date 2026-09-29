-- Prove2me | Theorems.Thm_PGLQuotient_twMass_succ
-- name    : PGLQuotient.twMass_succ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:47:30.875756+00:00
-- url     : https://prove2.me/theorems/71c23278-00a7-49b5-89f1-171cf2e771ec
-- title:
--   The row-peeling recursion for the twisted mass.
-- statement:
--   **The row-peeling recursion for the twisted mass.**
--
--   ```lean
--   theorem PGLQuotient.twMass_succ(hq : 1 < q) (n c j : ℕ) :
--       ∑' g : Vertex (n + 2), twWeight q c j g
--         = (q ^ (n + 1) * (q ^ (j + 1) - 1))⁻¹ *
--           (∑' g : Vertex (n + 1), twWeight q (c + 1) (j + 1) g
--             + (q ^ ((n + 1) * (c + 1)) - 1)⁻¹ * ∑' g : Vertex (n + 1), twWeight q (c + 1) 0 g) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PGLQuotient/VertexVolumeGeneral.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PGLQuotient/VertexVolumeGeneral.lean#L66

-- Thm stub generated from Algebra/PGLQuotient/VertexVolumeGeneral.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_TwistedWeight
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Definitions.Def_Algebra_PGLQuotient_VolumeAlgebra

/-!
# The vertex volume of the standard arithmetic quotient of `PGL_d`, in arbitrary rank

This file proves the headline computation in **arbitrary rank `d`**: with the Haar measure
normalised so that a maximal compact subgroup has volume `1`, the vertex volume of the standard
nonuniform arithmetic quotient of the affine Bruhat–Tits building of `PGL_d(F_q((t^{-1})))` is

`∑_λ 1/|Aut λ| = d / (P(d) · P(d-1))`,   `P(n) = ∏_{k=1}^{n} (q^k - 1)`

(`vertexVolume_general`, and `vertexVolume_general_rank` for the `d`-indexed form), together
with its `PGL`-normalised variant `(q-1) · ∑_λ 1/|Aut λ|` (`vertexVolume_general_pgl`).

The proof is the promised cut-set recursion, run on the two-parameter twisted mass of
`Algebra.PGLQuotient.TwistedWeight`:

* `twMass_succ`: peeling the top row of a dominant coweight turns the rank-`(n+2)` twisted mass
  into a combination of two rank-`(n+1)` twisted masses (the zero-gap branch and the
  positive-gap branch, the latter summed as a geometric series in the gap);
* `twMass_eq`: solving that recursion by induction on the rank, the closed form being
  `NumV/DenV` from `Algebra.PGLQuotient.VolumeAlgebra`;
* specialising `c = j = 0` gives the vertex volume, since `NumV q n 0 0 = (n+1)·P(n)` and
  `DenV q n 0 0 = P(n+1)·P(n)·P(n)`.

For `d = 2, 3` this recovers `heightZeta_rank_two` (at `s = 0`) and `vertexVolume_rank_three`.
-/

open PGLQuotient

open Finset

variable {q : ℝ}

theorem PGLQuotient.twMass_succ(hq : 1 < q) (n c j : ℕ) :
    ∑' g : Vertex (n + 2), twWeight q c j g
      = (q ^ (n + 1) * (q ^ (j + 1) - 1))⁻¹ *
        (∑' g : Vertex (n + 1), twWeight q (c + 1) (j + 1) g
          + (q ^ ((n + 1) * (c + 1)) - 1)⁻¹ * ∑' g : Vertex (n + 1), twWeight q (c + 1) 0 g) := by sorry
