-- Prove2me | solution 1 for MatrixCompletion.NoSpuriousMin.regularizer_hessian
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-14T00:29:28.903381+00:00
-- url     : https://prove2.me/submissions/e7b97ec6-c0f3-44de-899b-bc89ffe62c97

import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Matrix MatrixCompletion.NoSpuriousMin

namespace RegHess

/-! ### The positive part cubed is continuously differentiable -/

/-- `u ↦ (u)₊³` is differentiable at `0` with derivative `0`: glue the one-sided
derivatives, which are those of the zero function and of `u ↦ u³`. -/
lemma hasDerivAt_posPart_cube_zero : HasDerivAt (fun u : ℝ => max u 0 ^ 3) 0 (0 : ℝ) := by
  have hleft : HasDerivWithinAt (fun u : ℝ => max u 0 ^ 3) 0 (Set.Iic 0) 0 := by
    have h0 : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Set.Iic 0) 0 :=
      (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt
    refine h0.congr (fun u hu => ?_) (by simp)
    rw [max_eq_right (by simpa using hu)]; ring
  have hright : HasDerivWithinAt (fun u : ℝ => max u 0 ^ 3) 0 (Set.Ici 0) 0 := by
    have h3 : HasDerivWithinAt (fun u : ℝ => u ^ 3) 0 (Set.Ici 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).pow 3).hasDerivWithinAt
    refine h3.congr (fun u hu => ?_) (by simp)
    rw [max_eq_left (by simpa using hu)]
  have hu := hleft.union hright
  rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at hu

/-- `u ↦ (u)₊³` is differentiable everywhere, with derivative `3 (u)₊²`. -/
lemma hasDerivAt_posPart_cube (w : ℝ) :
    HasDerivAt (fun u : ℝ => max u 0 ^ 3) (3 * max w 0 ^ 2) w := by
  rcases lt_trichotomy w 0 with h | h | h
  · have heq : (fun u : ℝ => max u 0 ^ 3) =ᶠ[nhds w] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with u hu
      rw [max_eq_right (le_of_lt hu)]; ring
    have : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 w := hasDerivAt_const w 0
    rw [max_eq_right h.le]
    simpa using this.congr_of_eventuallyEq heq
  · subst h
    simpa using hasDerivAt_posPart_cube_zero
  · have heq : (fun u : ℝ => max u 0 ^ 3) =ᶠ[nhds w] fun u => u ^ 3 := by
      filter_upwards [Ioi_mem_nhds h] with u hu
      rw [max_eq_left (le_of_lt hu)]
    have hp : HasDerivAt (fun u : ℝ => u ^ 3) (3 * w ^ 2) w := by
      simpa using (hasDerivAt_id w).pow 3
    rw [max_eq_left h.le]
    exact hp.congr_of_eventuallyEq heq

/-- The scalar profile `G u = 4 (u−α)₊³ / u` appearing in the gradient. -/
lemma hasDerivAt_profile (α t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ => 4 * max (u - α) 0 ^ 3 / u)
      ((4 * (3 * max (t - α) 0 ^ 2) * t - 4 * max (t - α) 0 ^ 3) / t ^ 2) t := by
  have h1 : HasDerivAt (fun u : ℝ => max (u - α) 0 ^ 3) (3 * max (t - α) 0 ^ 2) t := by
    have := (hasDerivAt_posPart_cube (t - α)).comp t ((hasDerivAt_id t).sub_const α)
    simpa using this
  have h2 : HasDerivAt (fun u : ℝ => 4 * max (u - α) 0 ^ 3) (4 * (3 * max (t - α) 0 ^ 2)) t :=
    h1.const_mul 4
  simpa using h2.div (hasDerivAt_id t) ht

end RegHess

open RegHess

theorem solution {d r : ℕ} (α : ℝ) (hα : 0 < α) (X V : Matrix (Fin d) (Fin r) ℝ) :
    HasDerivAt (fun s : ℝ => innerM (regGrad α (X + s • V)) V) (regHessQF α X V) 0 := by
  classical
  set f : Fin d → ℝ → ℝ := fun i s =>
    (4 * max (rowNorm (X + s • V) i - α) 0 ^ 3 / rowNorm (X + s • V) i)
      * (∑ j, (X i j + s * V i j) * V i j) with hfdef
  -- The pairing splits as a sum over rows.
  have hfun : (fun s : ℝ => innerM (regGrad α (X + s • V)) V) = fun s : ℝ => ∑ i, f i s := by
    funext s
    simp only [hfdef, innerM, regGrad, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  -- The row norm along the line, as a square root of a quadratic.
  have hrho_eq : ∀ (i : Fin d) (s : ℝ),
      rowNorm (X + s • V) i = Real.sqrt (∑ j, (X i j + s * V i j) ^ 2) := by
    intro i s
    simp [rowNorm, vecNorm, Matrix.add_apply, Matrix.smul_apply]
  have hrho0 : ∀ i : Fin d, rowNorm (X + (0 : ℝ) • V) i = rowNorm X i := by
    intro i; simp
  have hq : ∀ i : Fin d, HasDerivAt (fun s : ℝ => ∑ j, (X i j + s * V i j) ^ 2)
      (2 * ∑ j, X i j * V i j) 0 := by
    intro i
    have hj : ∀ j : Fin r, HasDerivAt (fun s : ℝ => (X i j + s * V i j) ^ 2)
        (2 * (X i j * V i j)) 0 := by
      intro j
      have h1 : HasDerivAt (fun s : ℝ => X i j + s * V i j) (V i j) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (V i j)).const_add (X i j)
      simpa [mul_assoc] using h1.pow 2
    have hs := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => hj j)
    rw [Finset.mul_sum]
    exact hs
  have hp : ∀ i : Fin d, HasDerivAt (fun s : ℝ => ∑ j, (X i j + s * V i j) * V i j)
      (vecNorm (V i) ^ 2) 0 := by
    intro i
    have hj : ∀ j : Fin r, HasDerivAt (fun s : ℝ => (X i j + s * V i j) * V i j)
        (V i j * V i j) 0 := by
      intro j
      have h1 : HasDerivAt (fun s : ℝ => X i j + s * V i j) (V i j) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (V i j)).const_add (X i j)
      simpa using h1.mul_const (V i j)
    have hs := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => hj j)
    have hv : vecNorm (V i) ^ 2 = ∑ j, V i j * V i j := by
      rw [vecNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hv]
    convert hs using 1
  -- Row-wise derivative.
  have hrow : ∀ i : Fin d, HasDerivAt (f i)
      (12 * max (rowNorm X i - α) 0 ^ 2 * ((∑ j, X i j * V i j) / rowNorm X i) ^ 2
        + 4 * max (rowNorm X i - α) 0 ^ 3 / rowNorm X i
            * (vecNorm (V i) ^ 2 - ((∑ j, X i j * V i j) / rowNorm X i) ^ 2)) 0 := by
    intro i
    by_cases hlt : rowNorm X i < α
    · -- the regulariser is flat along this row near `s = 0`
      have hm : max (rowNorm X i - α) 0 = 0 := max_eq_right (by linarith)
      have hcont : ContinuousAt (fun s : ℝ => rowNorm (X + s • V) i) 0 := by
        have hc : ContinuousAt (fun s : ℝ => Real.sqrt (∑ j, (X i j + s * V i j) ^ 2)) 0 := by
          fun_prop
        simpa only [hrho_eq i] using hc
      have hev : ∀ᶠ s : ℝ in nhds (0 : ℝ), rowNorm (X + s • V) i < α := by
        have := hcont.tendsto
        rw [hrho0 i] at this
        exact this.eventually_lt_const hlt
      have hzero : f i =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℝ) := by
        filter_upwards [hev] with s hs
        have : max (rowNorm (X + s • V) i - α) 0 = 0 := max_eq_right (by linarith)
        simp [hfdef, this]
      have : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 (0 : ℝ) := hasDerivAt_const _ _
      rw [hm]
      simpa using this.congr_of_eventuallyEq hzero
    · push_neg at hlt
      have ht0 : (0 : ℝ) < rowNorm X i := lt_of_lt_of_le hα hlt
      have htne : rowNorm X i ≠ 0 := ne_of_gt ht0
      have hq0 : (∑ j, (X i j + (0 : ℝ) * V i j) ^ 2) = rowNorm X i ^ 2 := by
        simp only [zero_mul, add_zero]
        rw [rowNorm, vecNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      have hrho : HasDerivAt (fun s : ℝ => rowNorm (X + s • V) i)
          ((∑ j, X i j * V i j) / rowNorm X i) 0 := by
        have hne : (fun s : ℝ => ∑ j, (X i j + s * V i j) ^ 2) 0 ≠ 0 := by
          show (∑ j, (X i j + (0 : ℝ) * V i j) ^ 2) ≠ 0
          rw [hq0]; positivity
        have hs := (hq i).sqrt hne
        rw [hq0, Real.sqrt_sq ht0.le] at hs
        have hfe : (fun s : ℝ => Real.sqrt (∑ j, (X i j + s * V i j) ^ 2))
            = fun s : ℝ => rowNorm (X + s • V) i := by
          funext s; rw [hrho_eq i s]
        rw [hfe] at hs
        convert hs using 1
        field_simp
      have hG := hasDerivAt_profile α (rowNorm X i) htne
      have hcomp : HasDerivAt
          (fun s : ℝ => 4 * max (rowNorm (X + s • V) i - α) 0 ^ 3 / rowNorm (X + s • V) i)
          (((4 * (3 * max (rowNorm X i - α) 0 ^ 2) * rowNorm X i
              - 4 * max (rowNorm X i - α) 0 ^ 3) / rowNorm X i ^ 2)
            * ((∑ j, X i j * V i j) / rowNorm X i)) 0 := by
        have hc := HasDerivAt.comp (0 : ℝ) (by rw [hrho0 i] at *; exact hG) hrho
        simpa [Function.comp] using hc
      have hprod := hcomp.mul (hp i)
      have hval : (4 * max (rowNorm (X + (0 : ℝ) • V) i - α) 0 ^ 3
          / rowNorm (X + (0 : ℝ) • V) i) = 4 * max (rowNorm X i - α) 0 ^ 3 / rowNorm X i := by
        rw [hrho0 i]
      have hp0 : (∑ j, (X i j + (0 : ℝ) * V i j) * V i j) = ∑ j, X i j * V i j := by
        simp
      rw [hval, hp0] at hprod
      convert hprod using 1
      field_simp
      ring
  have hsum := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  rw [hfun]
  convert hsum using 1
