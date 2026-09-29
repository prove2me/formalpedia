-- Prove2me | solution 1 for PGLQuotient.heightZeta_unbounded_general
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:47:47.500513+00:00
-- url     : https://prove2.me/submissions/48976ef5-6671-47cf-b5a8-8e138299eaf4

-- Sol generated from Algebra/PGLQuotient/HeightZetaGeneral.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_HeightZetaGeneral
import Definitions.Def_Algebra_PGLQuotient_HeightZetaRankTwo
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_heightExp_ray
import Theorems.Thm_PGLQuotient_height_pow
import Theorems.Thm_PGLQuotient_pairExp_ray
import Theorems.Thm_PGLQuotient_rayVertex_injective
import Theorems.Thm_PGLQuotient_summable_weight_height_of_lt
import Theorems.Thm_PGLQuotient_vertexWeight_ge
import Theorems.Thm_PGLQuotient_vertexWeight_pos

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
theorem solution(hq : 1 < q) {d : ℕ} (hd : 2 ≤ d) (M : ℝ) :
    ∃ s : ℝ, s < d ∧ M < heightZeta q d s := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hd1 : (1:ℝ) ≤ ((d : ℝ) - 1) := by
    have : (2:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hd1pos : (0:ℝ) < ((d : ℝ) - 1) := by linarith
  have hdpos : (0:ℝ) < (d : ℝ) := by linarith
  set B : ℝ := (q ^ (d * d))⁻¹ with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  have hMpos : (0:ℝ) < |M| + 1 := by positivity
  set e : ℝ := min ((q - 1) / 2) (B * q / (((d : ℝ) - 1) * (|M| + 1))) with he
  have hepos : 0 < e := lt_min (by linarith) (by positivity)
  have he1 : e ≤ (q - 1) / 2 := min_le_left _ _
  have he2 : e ≤ B * q / (((d : ℝ) - 1) * (|M| + 1)) := min_le_right _ _
  have hwpos : 0 < q - e := by linarith
  have hw1 : 1 < q - e := by linarith
  set s : ℝ := (d : ℝ) * Real.logb q (q - e) with hs
  have hlogb : Real.logb q (q - e) < 1 := by
    have h := Real.logb_lt_logb hq hwpos (show q - e < q by linarith)
    rwa [Real.logb_self_eq_one hq] at h
  have hsd : s < d := by
    rw [hs]
    nlinarith
  refine ⟨s, hsd, ?_⟩
  -- the height weight
  have hsu : s / (d : ℝ) = Real.logb q (q - e) := by
    rw [hs]
    field_simp
  have hu : q ^ (s / (d : ℝ)) = q - e := by
    rw [hsu]
    exact Real.rpow_logb hq0 (ne_of_gt hq) hwpos
  set w : ℝ := q - e with hw
  set t : ℝ := (w / q) ^ (d - 1) with ht
  have hwq : w < q := by rw [hw]; linarith
  have hwnn : (0:ℝ) ≤ w := by rw [hw]; linarith
  have hratio0 : (0:ℝ) ≤ w / q := by positivity
  have hratio1 : w / q < 1 := by rw [div_lt_one hq0]; exact hwq
  have ht0 : (0:ℝ) ≤ t := by rw [ht]; positivity
  have ht1 : t < 1 := by
    rw [ht]
    exact pow_lt_one₀ hratio0 hratio1 (by omega)
  -- lower bound the zeta function by the cusp ray
  have hsummZ : Summable (fun g : Vertex d => vertexWeight q g * height q g ^ s) :=
    summable_weight_height_of_lt hq hd hsd
  have hnn : ∀ g : Vertex d, 0 ≤ vertexWeight q g * height q g ^ s := by
    intro g
    exact mul_nonneg (vertexWeight_pos g hq).le
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hq0 _) s).le
  have hray : ∀ n : ℕ, B * t ^ n
      ≤ vertexWeight q (rayVertex d n) * height q (rayVertex d n) ^ s := by
    intro n
    have hwt := vertexWeight_ge (rayVertex d n) hq
    rw [height_pow hq _ s, heightExp_ray hd, hu, pairExp_ray hd] at *
    have hkey : B * t ^ n = (q ^ (d * d))⁻¹ * (q ^ ((d - 1) * n))⁻¹ * w ^ ((d - 1) * n) := by
      rw [hB, ht, ← pow_mul, div_pow, div_eq_mul_inv]
      ring
    rw [hkey]
    exact mul_le_mul_of_nonneg_right hwt (by positivity)
  have hsummG : Summable (fun n : ℕ => B * t ^ n) :=
    (summable_geometric_of_lt_one ht0 ht1).mul_left B
  have hle : ∑' n : ℕ, B * t ^ n ≤ heightZeta q d s := by
    unfold heightZeta
    calc ∑' n : ℕ, B * t ^ n
        ≤ ∑' n : ℕ, vertexWeight q (rayVertex d n) * height q (rayVertex d n) ^ s :=
          hsummG.tsum_le_tsum hray
            (hsummZ.comp_injective (rayVertex_injective hd))
      _ ≤ ∑' g : Vertex d, vertexWeight q g * height q g ^ s :=
          tsum_comp_le_tsum_of_inj hsummZ hnn (rayVertex_injective hd)
  -- evaluate and estimate the geometric series
  have hgeomval : ∑' n : ℕ, B * t ^ n = B * (1 - t)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one ht0 ht1]
  have hbern : 1 - ((d : ℝ) - 1) * (e / q) ≤ t := by
    have hx : (-2:ℝ) ≤ -(e / q) := by
      have : e / q ≤ 1 := by
        rw [div_le_one hq0]; linarith
      linarith
    have := one_add_mul_le_pow hx (d - 1)
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      have : (1:ℕ) ≤ d := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast] at this
    have hrw : (1 : ℝ) + -(e / q) = w / q := by
      rw [hw]; field_simp; ring
    rw [hrw] at this
    rw [ht]
    linarith
  have h1t : 1 - t ≤ ((d : ℝ) - 1) * (e / q) := by linarith
  have h1tpos : (0:ℝ) < 1 - t := by linarith
  have hfinal : M < B * (1 - t)⁻¹ := by
    have hstep : B * (((d : ℝ) - 1) * (e / q))⁻¹ ≤ B * (1 - t)⁻¹ := by
      exact mul_le_mul_of_nonneg_left (inv_anti₀ h1tpos h1t) hBpos.le
    have hval : B * (((d : ℝ) - 1) * (e / q))⁻¹ = B * q / (((d : ℝ) - 1) * e) := by
      field_simp
    have hMlt : M < B * q / (((d : ℝ) - 1) * e) := by
      have hden : (0:ℝ) < ((d : ℝ) - 1) * e := by positivity
      rw [lt_div_iff₀ hden]
      have hkey : (((d : ℝ) - 1) * e) * (|M| + 1) ≤ B * q := by
        have : e * (((d : ℝ) - 1) * (|M| + 1)) ≤ B * q := by
          rw [← le_div_iff₀ (by positivity)]
          exact he2
        nlinarith
      nlinarith [le_abs_self M]
    linarith [hval ▸ hstep]
  linarith [hgeomval ▸ hle]
