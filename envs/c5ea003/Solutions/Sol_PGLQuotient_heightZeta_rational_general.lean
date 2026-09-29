-- Prove2me | solution 1 for PGLQuotient.heightZeta_rational_general
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:46:44.918133+00:00
-- url     : https://prove2.me/submissions/c9d25481-61ee-4963-b896-015f86817da0

-- Sol generated from Algebra/PGLQuotient/HeightZetaGeneral.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightZetaGeneral
import Definitions.Def_Algebra_PGLQuotient_HeightZetaRankTwo
import Definitions.Def_Algebra_PGLQuotient_TwistedWeight
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_height_pow
import Theorems.Thm_PGLQuotient_twWeight_zero_zero
import Theorems.Thm_PGLQuotient_twZ_rational

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
theorem solution(hq : 1 < q) {d : ℕ} (hd : 1 ≤ d) :
    ∃ P Q : Polynomial ℝ, ∀ s : ℝ, s < d →
      Q.eval (q ^ (s / (d : ℝ))) ≠ 0 ∧
        heightZeta q d s = P.eval (q ^ (s / (d : ℝ))) / Q.eval (q ^ (s / (d : ℝ))) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨P, Q, hPQ⟩ := twZ_rational (q := q) hq n 0 0
  refine ⟨P, Q, fun s hs => ?_⟩
  have hd0 : (0:ℝ) < ((n : ℝ) + 1) := by positivity
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hw0 : (0:ℝ) ≤ q ^ (s / ((n + 1 : ℕ) : ℝ)) := (Real.rpow_pos_of_pos hq0 _).le
  have hwq : q ^ (s / ((n + 1 : ℕ) : ℝ)) < q := by
    have h1 : s / ((n + 1 : ℕ) : ℝ) < 1 := by
      rw [hcast, div_lt_one hd0]
      rw [hcast] at hs
      exact hs
    calc q ^ (s / ((n + 1 : ℕ) : ℝ)) < q ^ (1:ℝ) := (Real.rpow_lt_rpow_left_iff hq).mpr h1
      _ = q := Real.rpow_one q
  obtain ⟨hQ, hZ⟩ := hPQ _ hw0 hwq
  refine ⟨hQ, ?_⟩
  rw [← hZ]
  unfold heightZeta
  refine tsum_congr (fun g => ?_)
  rw [height_pow hq g s]
  unfold twZ
  rw [twWeight_zero_zero]
  ring
