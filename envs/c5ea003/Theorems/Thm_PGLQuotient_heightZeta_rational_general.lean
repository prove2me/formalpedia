-- Prove2me | Theorems.Thm_PGLQuotient_heightZeta_rational_general
-- name    : PGLQuotient.heightZeta_rational_general
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:48:17.462887+00:00
-- url     : https://prove2.me/theorems/a25a4689-bc80-4c79-934c-8bb28e5045d2
-- title:
--   **The height zeta function of the rank-`d` quotient is a rational function of
-- statement:
--   **The height zeta function of the rank-`d` quotient is a rational function of
--   `u = q^{s/d}`** on the entire half-plane of convergence `s < d`.
--
--   ```lean
--   theorem PGLQuotient.heightZeta_rational_general(hq : 1 < q) {d : ℕ} (hd : 1 ≤ d) :
--       ∃ P Q : Polynomial ℝ, ∀ s : ℝ, s < d →
--         Q.eval (q ^ (s / (d : ℝ))) ≠ 0 ∧
--           heightZeta q d s = P.eval (q ^ (s / (d : ℝ))) / Q.eval (q ^ (s / (d : ℝ))) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PGLQuotient/HeightZetaGeneral.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PGLQuotient/HeightZetaGeneral.lean#L262

-- Thm stub generated from Algebra/PGLQuotient/HeightZetaGeneral.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightZetaGeneral
import Definitions.Def_Algebra_PGLQuotient_HeightZetaRankTwo

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







variable {w : ℝ}







open Polynomial

theorem PGLQuotient.heightZeta_rational_general(hq : 1 < q) {d : ℕ} (hd : 1 ≤ d) :
    ∃ P Q : Polynomial ℝ, ∀ s : ℝ, s < d →
      Q.eval (q ^ (s / (d : ℝ))) ≠ 0 ∧
        heightZeta q d s = P.eval (q ^ (s / (d : ℝ))) / Q.eval (q ^ (s / (d : ℝ))) := by sorry
