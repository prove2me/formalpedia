-- Prove2me | solution 1 for MatrixCompletion.NoSpuriousMin.no_spurious_local_minimum_corrected
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-14T19:05:23.598434+00:00
-- url     : https://prove2.me/submissions/67b719d3-c173-4aed-978b-011ba1e5e7fb

import Theorems.Thm_MatrixCompletion_NoSpuriousMin_optimality_conditions
import Theorems.Thm_MatrixCompletion_NoSpuriousMin_alignment_exists
import Theorems.Thm_MatrixCompletion_NoSpuriousMin_K_superlevel_bound_corrected
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_MatrixCompletion_NoSpuriousMin_row_norms_of_factorization
import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Instances.Matrix

open Matrix MatrixCompletion.NoSpuriousMin

namespace RootAux

variable {d r : ℕ}

lemma vecNorm_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ vecNorm x := Real.sqrt_nonneg _

lemma frobSq_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ frobSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma frobNorm_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : frobNorm A ^ 2 = frobSq A :=
  Real.sq_sqrt (frobSq_nonneg A)

lemma frobNorm_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ frobNorm A :=
  Real.sqrt_nonneg _

lemma eq_zero_of_frobSq_eq_zero {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} (h : frobSq A = 0) :
    A = 0 := by
  ext i j
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    fun k _ => Finset.sum_nonneg fun _ _ => sq_nonneg (A k _)).mp h i (Finset.mem_univ i)
  have := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => sq_nonneg (A i l)).mp hi j
    (Finset.mem_univ j)
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

lemma frobSq_eq_sum_rowNorm_sq (A : Matrix (Fin d) (Fin r) ℝ) :
    frobSq A = ∑ i, rowNorm A i ^ 2 := by
  simp only [frobSq, rowNorm, vecNorm]
  exact Finset.sum_congr rfl fun i _ =>
    (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm

lemma rowNorm_le_twoInftyNorm (A : Matrix (Fin d) (Fin r) ℝ) (i : Fin d) :
    rowNorm A i ≤ twoInftyNorm A :=
  le_ciSup (Set.Finite.bddAbove (Set.finite_range _)) i

lemma projSet_zero (Ω : Finset (Fin d × Fin d)) :
    projSet Ω (0 : Matrix (Fin d) (Fin d) ℝ) = 0 := by
  ext i j
  by_cases h : (i, j) ∈ Ω <;> simp [projSet, h]

end RootAux

open RootAux

set_option maxHeartbeats 1000000 in
theorem solution {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r)
    (Z X : Matrix (Fin d) (Fin r) ℝ) (Ω : Finset (Fin d × Fin d))
    (p μ κ lam α : ℝ)
    (hμ : 1 ≤ μ) (hκ : 1 ≤ κ) (hcond : sigmaMax Z ≤ κ * sigmaMin Z)
    (hσ : 0 < sigmaMin Z)
    (hinc : Incoherent μ Z) (hZnorm : frobSq Z = (r : ℝ))
    (hα1 : 100 * twoInftyNorm Z ≤ α) (hα2 : α ≤ 200 * twoInftyNorm Z)
    (hlam1 : 100 * sampDevNorm Ω p ≤ lam) (hlam2 : lam ≤ 200 * sampDevNorm Ω p)
    (hp : SampleCondition d r p μ κ)
    (hpC : 10 ^ 28 * μ ^ 4 * κ ^ 4 * (r : ℝ) ^ 2 * (1 + Real.log d) / d ≤ p)
    (hgood : GoodSample Z Ω p)
    (hmin : IsLocalMin (objective Z Ω lam α) X) :
    objective Z Ω lam α X = 0 ∧ X * Xᵀ = Z * Zᵀ := by
  classical
  -- Positivity of the tuning parameters, needed to invoke the optimality lemma.
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hZne : ∃ i, 0 < rowNorm Z i := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ i, rowNorm Z i = 0 := fun i => le_antisymm (hcon i) (vecNorm_nonneg _)
    have hz : frobSq Z = 0 := by rw [frobSq_eq_sum_rowNorm_sq]; simp [hall]
    rw [hZnorm] at hz
    linarith
  obtain ⟨i₀, hi₀⟩ := hZne
  have htwo : 0 < twoInftyNorm Z := lt_of_lt_of_le hi₀ (rowNorm_le_twoInftyNorm Z i₀)
  have hα0 : 0 < α := by linarith
  have hsdn : 0 ≤ sampDevNorm Ω p := Real.iSup_nonneg fun _ => vecNorm_nonneg _
  have hlam0 : 0 ≤ lam := by linarith
  -- `p` is positive: the sampling condition bounds it below by a positive quantity.
  have hp0 : 0 < p := by
    have hd1 : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
    have hlog : 0 < Real.log (d : ℝ) := Real.log_pos hd1
    have hμ0 : (0 : ℝ) < μ := by linarith
    have hκ0 : (0 : ℝ) < κ := by linarith
    have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
    have hnum : (0 : ℝ) < 10 ^ 10 * μ ^ 4 * κ ^ 4 * (r : ℝ) ^ 2 * Real.log (d : ℝ) :=
      mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hμ0 4)) (pow_pos hκ0 4))
        (pow_pos hrpos 2)) hlog
    have := div_pos hnum hdpos
    linarith [hp.1]
  -- Optimality conditions at the local minimum, and the aligned exact factor.
  obtain ⟨hfirst, hsecond⟩ :=
    MatrixCompletion.NoSpuriousMin.optimality_conditions Z X Ω lam α hlam0 hα0 hgood.symm hmin
  obtain ⟨U, hUU, hpsd⟩ := MatrixCompletion.NoSpuriousMin.alignment_exists Z X
  -- At a local minimum the auxiliary function is nonnegative.
  have hgradzero : innerM (objGrad Z Ω lam α X) (X - U) = 0 := by
    rw [hfirst]; simp [innerM]
  have hK0 : 0 ≤ Kfun Z Ω lam α X U := by
    rw [Kfun, hgradzero, hessQF]
    linarith [hsecond (X - U)]
  -- The negative-definite upper bound.
  have hKle := MatrixCompletion.NoSpuriousMin.K_superlevel_bound_corrected hd hr
    Z X U Ω p μ κ lam α
    hμ hκ hcond hσ hinc hZnorm hα1 hα2 hlam1 hlam2 hp hpC hgood hUU hpsd
  set a := frobNorm ((X - U)ᵀ * (X - U)) with ha
  set b := frobNorm ((X - U)ᵀ * U) with hb
  have ha2 : a ^ 2 = frobSq ((X - U)ᵀ * (X - U)) := frobNorm_sq _
  have hb2 : b ^ 2 = frobSq ((X - U)ᵀ * U) := frobNorm_sq _
  have hanneg : 0 ≤ a := frobNorm_nonneg _
  have hquad : 0 ≤ -(198 / 100) * a ^ 2 + (602 / 100) * a * b - 6 * b ^ 2 := by
    have hmul : 0 ≤ p * (-(198 / 100) * a ^ 2 + (602 / 100) * a * b - 6 * b ^ 2) := by
      rw [ha2, hb2]
      linarith [hK0, hKle]
    exact nonneg_of_mul_nonneg_right hmul hp0
  -- `−1999a² + 6001ab − 6000b²` is negative definite, so `a = b = 0`.
  have hbz : b = 0 := by nlinarith [sq_nonneg (198 * a - 301 * b), sq_nonneg b]
  have haz : a = 0 := by nlinarith [hbz, hanneg]
  -- Hence `X = U`.
  have hDD : (X - U)ᵀ * (X - U) = 0 :=
    eq_zero_of_frobSq_eq_zero (by rw [← ha2, haz]; ring)
  have hD : X - U = 0 := by
    ext k i
    have h0 : ((X - U)ᵀ * (X - U)) i i = 0 := by rw [hDD]; simp
    rw [Matrix.mul_apply] at h0
    simp only [Matrix.transpose_apply] at h0
    have := (Finset.sum_eq_zero_iff_of_nonneg
      fun l _ => mul_self_nonneg ((X - U) l i)).mp h0 k (Finset.mem_univ k)
    simpa using mul_self_eq_zero.mp this
  have hXU : X = U := sub_eq_zero.mp hD
  have hXX : X * Xᵀ = Z * Zᵀ := by rw [hXU]; exact hUU
  -- The regulariser vanishes: every row norm of `X` equals that of `Z`, which is at most `α`.
  have hreg : reg α X = 0 := by
    rw [reg]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hrow : rowNorm X i = rowNorm Z i := by
      rw [hXU]
      exact MatrixCompletion.NoSpuriousMin.row_norms_of_factorization U Z hUU i
    have hle : rowNorm X i ≤ α := by
      rw [hrow]
      have h1 := rowNorm_le_twoInftyNorm Z i
      linarith
    rw [hinge, max_eq_right (by linarith)]
    ring
  refine ⟨?_, hXX⟩
  rw [objective, hXX, sub_self, projSet_zero, hreg]
  simp [frobSq]
