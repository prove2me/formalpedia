-- Prove2me | solution 1 for mme_regional_scale_factor_log_div_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T23:40:44.160708+00:00
-- url     : https://prove2.me/submissions/3407f1a0-ecb3-4537-9207-dad1147d8195

import Definitions.Def_mme_regional_entropy_copy_bound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas

open BigOperators MME MME.RegionRate MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false

private theorem replicated_size_le {R : ℕ} (n : Fin R → ℕ) (k : ℕ) :
    (((∑ r, k * n r : ℕ) : ℝ) + 1) ≤
      ((k : ℝ) + 1) * (((∑ r, n r : ℕ) : ℝ) + 1) := by
  rw [← Finset.mul_sum, Nat.cast_mul]
  nlinarith [(Nat.cast_nonneg (∑ r, n r) : (0 : ℝ) ≤ _), (Nat.cast_nonneg k : (0 : ℝ) ≤ _)]

private theorem polynomial_factor_scale_le {R : ℕ}
    (n : Fin R → ℕ) (k degree : ℕ) :
    polynomialFactor (fun r => k * n r) degree ≤
      ((k : ℝ) + 1) ^ degree * polynomialFactor n degree := by
  unfold polynomialFactor
  calc
    _ ≤ (((k : ℝ) + 1) * (6 * (((∑ r, n r : ℕ) : ℝ) + 1))) ^ degree := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [replicated_size_le n k]
    _ = _ := mul_pow _ _ _

private theorem ambient_factor_scale_le {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (k : ℕ) :
    ambientFactor (half := half) (parent := parent) (fun r => k * n r) ≤
      ((k : ℝ) + 1) ^ Fintype.card (Cell half R parent) *
        ambientFactor (half := half) (parent := parent) n := by
  unfold ambientFactor
  calc
    _ ≤ (((k : ℝ) + 1) * (((∑ r, n r : ℕ) : ℝ) + 1)) ^
        Fintype.card (Cell half R parent) := by
      gcongr
      exact replicated_size_le n k
    _ = _ := mul_pow _ _ _

/-- With the repair scale and profile types fixed, the prefactor in the
hash-scale estimate grows polynomially under replication of the parent sizes. -/
private theorem mme_regional_scale_factor_polynomial_replication
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (d ell k : ℕ) :
    let degree := max (Fintype.card (Cell half R parent) + R * (half + 1))
      (R * (half + 1) + R * (half + 1) *
        Fintype.card (Fin 2 → CompleteSplit.CompleteWord ell))
    scaleFactor (half := half) (parent := parent) (fun r => k * n r) d ell ≤
      ((k : ℝ) + 1) ^ degree *
        scaleFactor (half := half) (parent := parent) n d ell := by
  dsimp only
  let c := Fintype.card (Cell half R parent)
  let a := R * (half + 1)
  let b := a * Fintype.card (Fin 2 → CompleteSplit.CompleteWord ell)
  let t : ℝ := k + 1
  have ht : 1 ≤ t := by dsimp [t]; exact le_add_of_nonneg_left (Nat.cast_nonneg k)
  have ht1 : 1 ≤ t ^ max (c + a) (a + b) := one_le_pow₀ ht
  have hca : t ^ (c + a) ≤ t ^ max (c + a) (a + b) :=
    pow_le_pow_right₀ ht (le_max_left _ _)
  have hab : t ^ (a + b) ≤ t ^ max (c + a) (a + b) :=
    pow_le_pow_right₀ ht (le_max_right _ _)
  have hfirst : ambientFactor (half := half) (parent := parent) (fun r => k * n r) *
      polynomialFactor (fun r => k * n r) a ≤
      t ^ max (c + a) (a + b) *
        (ambientFactor (half := half) (parent := parent) n * polynomialFactor n a) := by
    calc
      _ ≤ (t ^ c * ambientFactor (half := half) (parent := parent) n) *
          (t ^ a * polynomialFactor n a) := by
        apply mul_le_mul (ambient_factor_scale_le n k) (polynomial_factor_scale_le n k a)
        · unfold polynomialFactor; positivity
        · unfold ambientFactor; positivity
      _ = t ^ (c + a) *
          (ambientFactor (half := half) (parent := parent) n * polynomialFactor n a) := by
        rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hca (by
        unfold ambientFactor polynomialFactor; positivity)
  have hsecond : polynomialFactor (fun r => k * n r) a *
      polynomialFactor (fun r => k * n r) b ≤
      t ^ max (c + a) (a + b) * (polynomialFactor n a * polynomialFactor n b) := by
    calc
      _ ≤ (t ^ a * polynomialFactor n a) * (t ^ b * polynomialFactor n b) := by
        apply mul_le_mul (polynomial_factor_scale_le n k a) (polynomial_factor_scale_le n k b)
        · unfold polynomialFactor; positivity
        · unfold polynomialFactor; positivity
      _ = t ^ (a + b) * (polynomialFactor n a * polynomialFactor n b) := by
        rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hab (by unfold polynomialFactor; positivity)
  have hconst : (half : ℝ) + 2 ≤ t ^ max (c + a) (a + b) * ((half : ℝ) + 2) := by
    nlinarith [(Nat.cast_nonneg half : (0 : ℝ) ≤ _)]
  change (half : ℝ) + 2 + (8 * _ * _ + 128 * (d : ℝ) * _ * _) ≤ _
  dsimp only [scaleFactor, loadFactor]
  have hfirst' := mul_le_mul_of_nonneg_left hfirst (show (0 : ℝ) ≤ 8 by norm_num)
  have hsecond' := mul_le_mul_of_nonneg_left hsecond
    (show (0 : ℝ) ≤ 128 * (d : ℝ) by positivity)
  change (half : ℝ) + 2 + (8 * _ * _ + 128 * (d : ℝ) * _ * _) ≤
    t ^ max (c + a) (a + b) * ((half : ℝ) + 2 + (8 * _ * _ + 128 * (d : ℝ) * _ * _))
  nlinarith

open Filter

private theorem scale_factor_one_le {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (d ell : ℕ) :
    1 ≤ scaleFactor (half := half) (parent := parent) n d ell := by
  have hload : 0 ≤ loadFactor (half := half) (parent := parent) n d ell := by
    unfold loadFactor ambientFactor polynomialFactor
    positivity
  unfold scaleFactor
  linarith [Nat.cast_nonneg (α := ℝ) half]

/-- The explicit polynomial prefactor contributes zero logarithmic cost per
replicated block in the limit, for any fixed repair scale and profile types. -/
theorem solution
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (d ell : ℕ) :
    Tendsto (fun k : ℕ =>
      Real.log (scaleFactor (half := half) (parent := parent)
        (fun r => k * n r) d ell) / (k : ℝ)) atTop (nhds 0) := by
  let degree := max (Fintype.card (Cell half R parent) + R * (half + 1))
    (R * (half + 1) + R * (half + 1) *
      Fintype.card (Fin 2 → CompleteSplit.CompleteWord ell))
  let C := scaleFactor (half := half) (parent := parent) n d ell
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (scale_factor_one_le n d ell)
  have hlog (k : ℕ) :
      Real.log (scaleFactor (half := half) (parent := parent) (fun r => k * n r) d ell) ≤
        (degree : ℝ) * Real.log ((k : ℝ) + 1) + Real.log C := by
    have hpos : 0 < scaleFactor (half := half) (parent := parent) (fun r => k * n r) d ell :=
      lt_of_lt_of_le zero_lt_one (scale_factor_one_le _ d ell)
    have h := Real.log_le_log hpos (mme_regional_scale_factor_polynomial_replication n d ell k)
    rw [Real.log_mul (pow_ne_zero _ (by positivity)) hC.ne', Real.log_pow] at h
    exact h
  have hloglim : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) / (k : ℝ)) atTop (nhds 0) := by
    have ht : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp ht
  have hinv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun k : ℕ =>
      ((degree : ℝ) * Real.log ((k : ℝ) + 1) + Real.log C) / (k : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero, add_zero, add_div, mul_div_assoc, div_eq_mul_inv, add_mul, mul_assoc] using
      (hloglim.const_mul (degree : ℝ)).add (hinv.const_mul (Real.log C))
  apply squeeze_zero (fun k => div_nonneg
    (Real.log_nonneg (scale_factor_one_le _ d ell)) (Nat.cast_nonneg k))
    (fun k => div_le_div_of_nonneg_right (hlog k) (Nat.cast_nonneg k)) hupper


#print axioms solution
