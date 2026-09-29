-- Prove2me | solution 1 for PGLQuotient.cuspTail_lower
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:28:12.525971+00:00
-- url     : https://prove2.me/submissions/6b8c807b-2db4-49cf-a77e-f5d989aa7f3c

-- Sol generated from Algebra/PGLQuotient/CuspTail.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_heightExp_ray
import Theorems.Thm_PGLQuotient_height_gt_iff
import Theorems.Thm_PGLQuotient_pairExp_ray
import Theorems.Thm_PGLQuotient_summable_vertexWeight
import Theorems.Thm_PGLQuotient_vertexWeight_ge
import Theorems.Thm_PGLQuotient_vertexWeight_pos

/-!
# The sharp cusp-tail estimate of order `T^{-d}`

For the standard arithmetic quotient of the Bruhat–Tits building of `PGL_d(F_q((t^{-1})))`,
with the normalised lattice-minima height `α` of `Algebra.PGLQuotient.VertexModel`, we prove
the two-sided cusp-tail estimate

`c · T^{-d} ≤ mass {α > T} ≤ C · T^{-d}`   for all `T ≥ 1`.

The upper bound is the delicate half: the naive estimate coming from the integrability
threshold only gives `T^{-r}` for every `r < d`.  The sharp exponent is obtained by
*fibering the gap lattice over the height exponent*: the linear form
`N(g) = ∑_k (d-1-k) g_k = d log_q α` determines the first gap coordinate `g_0` once the
remaining coordinates are known, and the residual exponent `R(g) = ∑_k k(d-1-k) g_k` does not
involve `g_0` at all.  Hence `∑_{N(g) = n} q^{-R(g)}` is bounded uniformly in `n`, and
summing the resulting geometric series in `n` produces the exact exponent `T^{-d}`.

The lower bound comes from a single vertex on the cusp ray `λ = (n, 0, …, 0)`.
-/

open PGLQuotient

open Finset

variable {d : ℕ} {q : ℝ}



/-! ### The fibering majorant -/









/-! ### From the fibered bound to the sharp `T^{-d}` cusp tail -/






open PGLQuotient in
theorem solution(hq : 1 < q) (hd : 2 ≤ d) :
    ∃ c > 0, ∀ T : ℝ, 1 ≤ T → c * T ^ (-(d:ℝ)) ≤ cuspTail q d T := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hd1 : (1:ℝ) < (d : ℝ) := by
    have : 1 < d := by omega
    exact_mod_cast this
  have hd0 : (0:ℝ) < (d : ℝ) := lt_trans zero_lt_one hd1
  have hdne : (d : ℝ) - 1 ≠ 0 := by linarith
  have hdpos : (0:ℝ) < (d : ℝ) - 1 := by linarith
  refine ⟨(q ^ (d * d))⁻¹ * (q ^ (d - 1))⁻¹, by positivity, ?_⟩
  intro T hT
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  set L : ℝ := Real.logb q T with hL
  have hL0 : 0 ≤ L := Real.logb_nonneg hq hT
  have hTq : q ^ L = T := Real.rpow_logb hq0 (ne_of_gt hq) hT0
  have hdm1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    have h1 : 1 ≤ d := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have hquot0 : (0:ℝ) ≤ (d : ℝ) * L / ((d : ℝ) - 1) :=
    div_nonneg (by positivity) (le_of_lt hdpos)
  set n : ℕ := ⌊(d : ℝ) * L / ((d : ℝ) - 1)⌋₊ + 1 with hn
  have hnlow : (d : ℝ) * L / ((d : ℝ) - 1) < (n : ℝ) := by
    rw [hn]
    push_cast
    exact Nat.lt_floor_add_one _
  have hnup : ((d - 1 : ℕ) : ℝ) * (n : ℝ) ≤ (d : ℝ) * L + ((d : ℝ) - 1) := by
    have h1 : (n : ℝ) ≤ (d : ℝ) * L / ((d : ℝ) - 1) + 1 := by
      rw [hn]
      push_cast
      linarith [Nat.floor_le hquot0]
    have h2 : ((d : ℝ) - 1) * ((d : ℝ) * L / ((d : ℝ) - 1) + 1) = (d : ℝ) * L + ((d : ℝ) - 1) := by
      field_simp
    rw [hdm1]
    nlinarith [h1, hdpos]
  have hheight : T < height q (rayVertex d n) := by
    refine (height_gt_iff hq hd hT _).mpr ?_
    rw [heightExp_ray hd]
    push_cast
    rw [hdm1]
    rw [div_lt_iff₀ hdpos] at hnlow
    linarith
  have hsum0 := summable_vertexWeight (q := q) (d := d) hq hd
  have hsub1 : Summable (fun g : {g : Vertex d | T < height q g} =>
      vertexWeight q (g : Vertex d)) := hsum0.subtype _
  have hterm : vertexWeight q (rayVertex d n) ≤ cuspTail q d T :=
    hsub1.le_tsum (⟨rayVertex d n, hheight⟩ : {g : Vertex d | T < height q g})
      (fun j _ => le_of_lt (vertexWeight_pos _ hq))
  refine le_trans ?_ hterm
  have hw := vertexWeight_ge (q := q) (rayVertex d n) hq
  rw [pairExp_ray hd] at hw
  refine le_trans ?_ hw
  have hpowbound : q ^ ((d - 1) * n) ≤ q ^ (d - 1) * T ^ (d:ℝ) := by
    have h1 : q ^ ((d - 1) * n) = q ^ (((d - 1 : ℕ) : ℝ) * (n : ℝ)) := by
      rw [← Real.rpow_natCast q ((d - 1) * n)]
      push_cast
      ring_nf
    have h2 : q ^ (d - 1) * T ^ (d:ℝ) = q ^ (((d : ℝ) - 1) + (d : ℝ) * L) := by
      rw [Real.rpow_add hq0, ← hTq, ← Real.rpow_mul (le_of_lt hq0), ← hdm1,
        ← Real.rpow_natCast q (d - 1)]
      ring_nf
    rw [h1, h2]
    refine (Real.rpow_le_rpow_left_iff hq).mpr ?_
    linarith [hnup]
  have hstep : (q ^ (d - 1))⁻¹ * T ^ (-(d:ℝ)) ≤ (q ^ ((d - 1) * n))⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hT0), ← mul_inv]
    exact inv_anti₀ (pow_pos hq0 _) hpowbound
  calc (q ^ (d * d))⁻¹ * (q ^ (d - 1))⁻¹ * T ^ (-(d:ℝ))
      = (q ^ (d * d))⁻¹ * ((q ^ (d - 1))⁻¹ * T ^ (-(d:ℝ))) := by ring
    _ ≤ (q ^ (d * d))⁻¹ * (q ^ ((d - 1) * n))⁻¹ := by
        refine mul_le_mul_of_nonneg_left hstep (by positivity)
