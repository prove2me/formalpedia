-- Prove2me | solution 1 for PGLQuotient.prod_gapRatioW
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:38:57.27822+00:00
-- url     : https://prove2.me/submissions/cc68fb84-8616-43d9-8189-a4ed0d590d9d

-- Sol generated from Algebra/PGLQuotient/HeightZetaGeneral.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightZetaGeneral
import Definitions.Def_Algebra_PGLQuotient_HeightZetaRankTwo
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_gapAt_coe

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








open PGLQuotient in
theorem solution(w : ℝ) (g : Vertex d) :
    ∏ k, gapRatioW q d w k ^ g k = (q ^ pairExp g)⁻¹ * w ^ heightExp g := by
  have hterm : ∀ k : Fin (d - 1), gapRatioW q d w k ^ g k
      = (q⁻¹) ^ ((((k : ℕ) + 1) * (d - 1 - (k : ℕ))) * g k)
        * w ^ ((d - 1 - (k : ℕ)) * g k) := by
    intro k
    unfold gapRatioW
    rw [mul_pow, ← inv_pow, ← pow_mul, ← pow_mul]
  rw [Finset.prod_congr rfl (fun k _ => hterm k), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, ← inv_pow]
  congr 2
  · rw [pairExp, ← Fin.sum_univ_eq_sum_range (fun k => (k + 1) * (d - 1 - k) * gapAt g k)]
    exact Finset.sum_congr rfl (fun k _ => by rw [gapAt_coe, mul_assoc])
  · rw [heightExp, ← Fin.sum_univ_eq_sum_range (fun k => (d - 1 - k) * gapAt g k)]
    exact Finset.sum_congr rfl (fun k _ => by rw [gapAt_coe])
