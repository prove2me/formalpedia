-- Prove2me | solution 1 for mme_regional_entropy_expression_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T23:43:52.973514+00:00
-- url     : https://prove2.me/submissions/9ff07fe7-7b21-410d-9614-5e000f31cec2

import Definitions.Def_mme_regional_entropy_copy_bound
import Theorems.Thm_mme_regional_mass_entropy_algebra
import Mathlib.Tactic.Ring
import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas

open scoped Classical
open BigOperators MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false

/-- Replicating every occurrence preserves each normalized child profile. -/
private theorem mme_cell_frequency_scale
    {C W : Type*} [Fintype W] (mu : C → W → ℕ)
    (k : ℕ) (hk : 0 < k) (c : C) (w : W) :
    cellFrequency (fun c w => k * mu c w) c w = cellFrequency mu c w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [cellFrequency, ← Finset.mul_sum, Nat.cast_mul]
  exact mul_div_mul_left _ _ hk'

/-- Uniform replication preserves the regional parent-mixture centers. -/
private theorem mme_parent_mixture_scale
    {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (k : ℕ) (hk : 0 < k) (r : Fin R) (w : Fin 2 → W) :
    parentMixture htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun c v => k * mu c v) r w = parentMixture htotal n m mu r w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [parentMixture, mme_cell_frequency_scale mu k hk, Nat.cast_mul,
    mul_assoc, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hk'


open MME.RegionRate

private theorem mass_entropy_scale {W : Type*} [Fintype W] (k : ℕ) (x : W → ℕ) :
    massEntropy (fun w => ((k * x w : ℕ) : ℝ)) =
      (k : ℝ) * massEntropy (fun w => (x w : ℝ)) := by
  simpa only [Nat.cast_mul] using
    (mme_regional_mass_entropy_algebra (C := Unit) (W := W)).1 (k : ℝ)
      (fun w => (x w : ℝ))

private theorem potential_scale {C W : Type*} [Fintype C] [Fintype W]
    (k : ℕ) (mu : C → W → ℕ) :
    potential (fun c w => k * mu c w) = (k : ℝ) * potential mu := by
  rw [(mme_regional_mass_entropy_algebra (C := C) (W := W)).2.2,
    (mme_regional_mass_entropy_algebra (C := C) (W := W)).2.2,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun c _ => mass_entropy_scale k (mu c))

private theorem part_count_scale {C W G : Type*} [Fintype C]
    (boundary : C → Prop) (group : C → G) (mu : C → W → ℕ)
    (k : ℕ) (s : {c : C // boundary c} ⊕ G) (w : W) :
    partCount boundary group (fun c w => k * mu c w) s w =
      k * partCount boundary group mu s w := by
  classical
  cases s with
  | inl c => rfl
  | inr g => simp [partCount, Finset.mul_sum, mul_ite]

/-- Replicating the regional split counts multiplies their joint entropy
by the replication factor, including profiles with zero counts. -/
private theorem mme_regional_joint_potential_scale {half R : ℕ}
    {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (k : ℕ) :
    jointPotential (fun r c => k * m r c) = (k : ℝ) * jointPotential m := by
  simp only [jointPotential, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun r _ => mass_entropy_scale k (m r))

private theorem coarse_potential_scale {half R : ℕ}
    {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (k : ℕ) (i : Fin 3) :
    coarsePotential (fun r c => k * m r c) i = (k : ℝ) * coarsePotential m i := by
  simp only [coarsePotential, marginalCounts, ← Finset.mul_sum]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun r _ => mass_entropy_scale k _)

private theorem penalty_potential_scale {half R : ℕ}
    {parent : Fin R → Fin 3 → ℕ} (n : Fin R → ℕ)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (k : ℕ) (hk : 0 < k) :
    penaltyPotential (fun r => k * n r) (fun r c => k * m r c) =
      (k : ℝ) * penaltyPotential n m := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [penaltyPotential, Nat.cast_mul, mul_div_mul_left _ _ hk',
    mul_assoc, Finset.mul_sum]

private theorem parent_potential_scale {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ) (k : ℕ) (hk : 0 < k) :
    parentPotential htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun c w => k * mu c w) = (k : ℝ) * parentPotential htotal n m mu := by
  have heq (r : Fin R) :
      parentMixture htotal (fun r => k * n r) (fun r c => k * m r c)
        (fun c w => k * mu c w) r = parentMixture htotal n m mu r := by
    funext w
    exact mme_parent_mixture_scale htotal n m mu k hk r w
  simp only [parentPotential, heq, Nat.cast_mul, mul_assoc, Finset.mul_sum]

private theorem compatibility_potential_scale {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ} (i : Fin 2)
    (mu : Cell half R parent → W → ℕ) (k : ℕ) :
    compatibilityPotential i (fun c w => k * mu c w) =
      (k : ℝ) * compatibilityPotential i mu := by
  simp only [compatibilityPotential]
  have heq : partCount (yzBoundary i) (modeGroup (yzMode i)) (fun c w => k * mu c w) =
      fun s w => k * partCount (yzBoundary i) (modeGroup (yzMode i)) mu s w := by
    funext s w
    exact part_count_scale _ _ _ _ _ _
  rw [heq, potential_scale]

/-- Uniform replication scales the minimum of the three summed regional
rates exactly; normalized parent profiles and entropy penalties are unchanged. -/
private theorem mme_regional_rate_scale {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → W → ℕ) (k : ℕ) (hk : 0 < k) :
    regionalRate htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun i c w => k * mu i c w) = (k : ℝ) * regionalRate htotal n m mu := by
  simp only [regionalRate, coarse_potential_scale, penalty_potential_scale n m k hk,
    parent_potential_scale htotal n m _ k hk, compatibility_potential_scale,
    ← mul_sub, mul_min_of_nonneg _ _ (Nat.cast_nonneg k)]

/-- The entropy exponent controlling the hash scale is linear under uniform
replication, with the tolerance fixed before choosing the replication factor. -/
private theorem mme_regional_scale_exponent_scale {half R ell : ℕ}
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (eps : ℝ) (k : ℕ) (hk : 0 < k) :
    scaleExponent htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun i c w => k * mu i c w) eps =
        (k : ℝ) * scaleExponent htotal n m mu eps := by
  rw [scaleExponent, scaleExponent, mme_regional_joint_potential_scale,
    mme_regional_rate_scale htotal n m mu k hk]
  simp only [← Finset.mul_sum, Nat.cast_mul]
  ring


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
private theorem mme_regional_scale_factor_log_div_tendsto_zero
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


private theorem polynomial_factor_log_div_tendsto_zero {R : ℕ}
    (n : Fin R → ℕ) (degree : ℕ) :
    Tendsto (fun k : ℕ => Real.log (polynomialFactor (fun r => k * n r) degree) /
      (k : ℝ)) atTop (nhds 0) := by
  have hpos (m : Fin R → ℕ) : 0 < polynomialFactor m degree := by
    unfold polynomialFactor
    positivity
  have hone (m : Fin R → ℕ) : 1 ≤ polynomialFactor m degree := by
    apply one_le_pow₀
    nlinarith [Nat.cast_nonneg (α := ℝ) (∑ r, m r)]
  have hlog (k : ℕ) :
      Real.log (polynomialFactor (fun r => k * n r) degree) ≤
        (degree : ℝ) * Real.log ((k : ℝ) + 1) + Real.log (polynomialFactor n degree) := by
    have h := Real.log_le_log (hpos _) (polynomial_factor_scale_le n k degree)
    rw [Real.log_mul (pow_ne_zero _ (by positivity)) (hpos n).ne', Real.log_pow] at h
    exact h
  have hloglim : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) / (k : ℝ)) atTop (nhds 0) := by
    have ht : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp ht
  have hinv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun k : ℕ =>
      ((degree : ℝ) * Real.log ((k : ℝ) + 1) + Real.log (polynomialFactor n degree)) /
        (k : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero, add_zero, add_div, mul_div_assoc, div_eq_mul_inv, add_mul,
      mul_assoc] using
      (hloglim.const_mul (degree : ℝ)).add (hinv.const_mul (Real.log (polynomialFactor n degree)))
  exact squeeze_zero (fun k => div_nonneg (Real.log_nonneg (hone _)) (Nat.cast_nonneg k))
    (fun k => div_le_div_of_nonneg_right (hlog k) (Nat.cast_nonneg k)) hupper

private theorem sqrt_div_tendsto_zero_of_linear_rate (x : ℕ → ℝ) (rate : ℝ)
    (hx : Tendsto (fun k : ℕ => x k / (k : ℝ)) atTop (nhds rate)) :
    Tendsto (fun k : ℕ => Real.sqrt (x k) / (k : ℝ)) atTop (nhds 0) := by
  have hi : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun k : ℕ => x k / (k : ℝ)^2) atTop (nhds 0) := by
    simpa [div_eq_mul_inv, pow_two, mul_assoc] using hx.mul hi
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_div' _ (sq_nonneg _),
    Real.sqrt_sq (Nat.cast_nonneg _)] using h

/-- The explicit entropy lower-bound expression has the regional rate minus
its fixed-tolerance entropy loss as its asymptotic logarithmic rate. Polynomial
prefactors and the progression loss contribute zero per replicated block. -/
theorem solution
    {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (eps : ℝ) (d : ℕ) :
    let size := fun k r => k * n r
    let counts := fun k r c => k * m r c
    let profiles := fun k i c w => k * mu i c w
    let E := fun k => regionalRate htotal (size k) (counts k) (profiles k)
    let loss := fun k => ((∑ r, size k r : ℕ) : ℝ) *
      entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) eps
    let theta := fun k => scaleExponent htotal (size k) (counts k) (profiles k) eps
    let factor := fun k => scaleFactor (half := half) (parent := parent) (size k) d ell
    Tendsto (fun k : ℕ =>
      Real.log (Real.exp (E k - loss k - 4 * Real.sqrt (Real.log (factor k) + theta k)) /
        (32 * polynomialFactor (size k) (Fintype.card (Cell half R parent)) * factor k)) /
          (k : ℝ)) atTop
      (nhds (regionalRate htotal n m mu - ((∑ r, n r : ℕ) : ℝ) *
        entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) eps)) := by
  dsimp only
  let rate := regionalRate htotal n m mu
  let loss := ((∑ r, n r : ℕ) : ℝ) *
    entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) eps
  let theta := scaleExponent htotal n m mu eps
  let factor := fun k => scaleFactor (half := half) (parent := parent) (fun r => k * n r) d ell
  let poly := fun k => polynomialFactor (fun r => k * n r) (Fintype.card (Cell half R parent))
  have hfac := mme_regional_scale_factor_log_div_tendsto_zero (half := half) (parent := parent) n d ell
  have hpoly := polynomial_factor_log_div_tendsto_zero n (Fintype.card (Cell half R parent))
  have hi : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have htheta : Tendsto (fun k : ℕ =>
      (Real.log (factor k) + (k : ℝ) * theta) / (k : ℝ)) atTop (nhds theta) := by
    have h := hfac.add_const theta
    convert h.congr' ?_ using 1
    · simp
    · filter_upwards [eventually_gt_atTop 0] with k hk
      have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      dsimp [factor]
      field_simp
  have hsqrt := sqrt_div_tendsto_zero_of_linear_rate _ theta htheta
  have hmain := (((tendsto_const_nhds (x := rate - loss)).sub (hsqrt.const_mul 4)).sub
    (hi.const_mul (Real.log 32))).sub hpoly |>.sub hfac
  convert hmain.congr' ?_ using 1
  · simp [rate, loss]
  · filter_upwards [eventually_gt_atTop 0] with k hk
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hfactor : 0 < factor k :=
      lt_of_lt_of_le zero_lt_one (scale_factor_one_le _ d ell)
    have hpol : 0 < poly k := by dsimp [poly, polynomialFactor]; positivity
    rw [Real.log_div (Real.exp_ne_zero _) (mul_ne_zero
      (mul_ne_zero (by norm_num) hpol.ne') hfactor.ne'), Real.log_exp,
      Real.log_mul (mul_ne_zero (by norm_num) hpol.ne') hfactor.ne',
      Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) hpol.ne']
    rw [mme_regional_rate_scale htotal n m mu k hk,
      mme_regional_scale_exponent_scale htotal n m mu eps k hk]
    simp only [← Finset.mul_sum, Nat.cast_mul]
    dsimp only [rate, loss, theta, factor, poly] at *
    field_simp
    ring


#print axioms solution
