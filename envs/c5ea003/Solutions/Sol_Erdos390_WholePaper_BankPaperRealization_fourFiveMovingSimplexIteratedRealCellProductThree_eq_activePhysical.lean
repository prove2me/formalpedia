-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.fourFiveMovingSimplexIteratedRealCellProductThree_eq_activePhysical
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:54:21.273668+00:00
-- url     : https://prove2.me/submissions/ed7587b0-826a-4e79-8336-a913ee191de1

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_009

/- Source module: Erdos390.WholePaper.BankPaperFourFiveMovingFaceCellOscillation -/
section


/-!
# Log-log cells at the strict moving face

The continuum replacement in the four/five chamber is a finite collection
of the paper's literal cells `(n-1,n]`, with measure `dx/(x log x)`.  This
file proves the right-endpoint quadrature estimate for the one-dimensional
conditional moving-face kernel.

There are two contributions.  On cells whose right endpoint is active, the
reciprocal kernel is increasing and the cell oscillations telescope to at
most one.  There is at most one further cell whose interior is active while
its right endpoint is inactive; that unique strict-face cell costs at most
one.  Thus the total oscillation envelope is at most two.  Since every
paper cell has mass at most

`delta_A = 1 / (A log A)`,

the finite cell quadrature defect is at most `2 delta_A`.  No limiting mesh
or convergence hypothesis occurs.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## The real conditional moving face -/











theorem fourFiveRealMovingFaceReciprocal_nonneg_le_one
    {y : Nat} {u c x : Real}
    (hface : fourFiveRealLogCoordinate y x < u - c - 1) :
    0 <= fourFiveRealMovingFaceReciprocal y u c x ∧
      fourFiveRealMovingFaceReciprocal y u c x <= 1 := by
  have hden : 1 < u - c - fourFiveRealLogCoordinate y x := by
    linarith
  constructor
  · unfold fourFiveRealMovingFaceReciprocal
    exact inv_nonneg.mpr (zero_le_one.trans hden.le)
  · unfold fourFiveRealMovingFaceReciprocal
    simpa only [inv_one] using
      (inv_le_inv₀ (zero_lt_one.trans hden) zero_lt_one).mpr hden.le

theorem fourFiveRealMovingFaceKernel_nonneg_le_one
    {A y : Nat} {u c x : Real} :
    0 <= fourFiveRealMovingFaceKernel A y u c x ∧
      fourFiveRealMovingFaceKernel A y u c x <= 1 := by
  unfold fourFiveRealMovingFaceKernel
  split_ifs with h
  · exact fourFiveRealMovingFaceReciprocal_nonneg_le_one h.2
  · exact ⟨le_rfl, zero_le_one⟩

theorem measurable_fourFiveRealLogCoordinate (y : Nat) :
    Measurable (fourFiveRealLogCoordinate y) := by
  unfold fourFiveRealLogCoordinate
  exact Real.measurable_log.div measurable_const

theorem measurable_fourFiveRealMovingFaceKernel
    (A y : Nat) (u c : Real) :
    Measurable (fourFiveRealMovingFaceKernel A y u c) := by
  have hcoord := measurable_fourFiveRealLogCoordinate y
  have hactive : MeasurableSet
      {x : Real | (A : Real) < x ∧
        fourFiveRealLogCoordinate y x < u - c - 1} :=
    measurableSet_Ioi.inter (hcoord measurableSet_Iio)
  have hrecip : Measurable
      (fourFiveRealMovingFaceReciprocal y u c) := by
    unfold fourFiveRealMovingFaceReciprocal
    exact ((measurable_const.sub measurable_const).sub hcoord).inv
  unfold fourFiveRealMovingFaceKernel
  exact Measurable.ite hactive hrecip measurable_const

theorem measurable_fourFiveLogLogLebesgueDensity :
    Measurable fourFiveLogLogLebesgueDensity := by
  unfold fourFiveLogLogLebesgueDensity
  exact measurable_const.div
    (measurable_id.mul Real.measurable_log)



/-! ## The unique cell crossed by the strict face -/









/-! ## A two-unit finite oscillation envelope -/

















/-! ## Pointwise right-endpoint control -/



/-! ## The mesh is derived from the literal paper cells -/



theorem fourFiveLogLogCellMeshBound_pos
    {A : Nat} (hA : 2 <= A) :
    0 < fourFiveLogLogCellMeshBound A := by
  have hAreal : 0 < (A : Real) := by positivity
  have hlog : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  unfold fourFiveLogLogCellMeshBound
  positivity

theorem fourFiveLogLogLebesgueDensity_le_meshBound
    {A n : Nat} {x : Real} (hA : 2 <= A) (hAn : A < n)
    (hx : x ∈ Set.Icc (((n - 1 : Nat) : Real)) (n : Real)) :
    0 <= fourFiveLogLogLebesgueDensity x ∧
      fourFiveLogLogLebesgueDensity x <= fourFiveLogLogCellMeshBound A := by
  have hAn1 : A <= n - 1 := by omega
  have hAx : (A : Real) <= x :=
    (by exact_mod_cast hAn1 : (A : Real) <= ((n - 1 : Nat) : Real))
      |>.trans hx.1
  have hApos : 0 < (A : Real) := by positivity
  have hxpos : 0 < x := hApos.trans_le hAx
  have hlogA : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlogmono : Real.log (A : Real) <= Real.log x :=
    Real.log_le_log hApos hAx
  have hlogx : 0 < Real.log x := hlogA.trans_le hlogmono
  have hdenle :
      (A : Real) * Real.log (A : Real) <= x * Real.log x := by
    exact mul_le_mul hAx hlogmono hlogA.le hxpos.le
  unfold fourFiveLogLogLebesgueDensity fourFiveLogLogCellMeshBound
  constructor
  · positivity
  · exact one_div_le_one_div_of_le (mul_pos hApos hlogA) hdenle







theorem intervalIntegrable_fourFiveDensity_mul_realMovingFace_cell
    {A Y y n : Nat} {u c : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hn : n ∈ Finset.Ioc A Y) :
    IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        fourFiveRealMovingFaceKernel A y u c x)
      volume (((n - 1 : Nat) : Real)) (n : Real) := by
  have hA : 2 <= A := hy.trans hyA
  have hab : (((n - 1 : Nat) : Real)) <= (n : Real) := by
    exact_mod_cast Nat.sub_le n 1
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  let mu : Measure Real :=
    volume.restrict
      (Set.Icc (((n - 1 : Nat) : Real)) (n : Real))
  have hdelta0 : 0 <= fourFiveLogLogCellMeshBound A :=
    (fourFiveLogLogCellMeshBound_pos hA).le
  have hconst : Integrable
      (fun _ : Real => fourFiveLogLogCellMeshBound A) mu := by
    exact integrable_const _
  have hmeas : Measurable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        fourFiveRealMovingFaceKernel A y u c x) :=
    measurable_fourFiveLogLogLebesgueDensity.mul
      (measurable_fourFiveRealMovingFaceKernel A y u c)
  apply hconst.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs, abs_mul]
  have hdensity := fourFiveLogLogLebesgueDensity_le_meshBound hA
    (Finset.mem_Ioc.mp hn).1 hx
  have hkernel := fourFiveRealMovingFaceKernel_nonneg_le_one
    (A := A) (y := y) (u := u) (c := c) (x := x)
  rw [abs_of_nonneg hdensity.1, abs_of_nonneg hkernel.1]
  calc
    fourFiveLogLogLebesgueDensity x *
        fourFiveRealMovingFaceKernel A y u c x <=
      fourFiveLogLogCellMeshBound A *
        fourFiveRealMovingFaceKernel A y u c x :=
      mul_le_mul_of_nonneg_right hdensity.2 hkernel.1
    _ <= fourFiveLogLogCellMeshBound A * 1 :=
      mul_le_mul_of_nonneg_left hkernel.2 hdelta0
    _ = fourFiveLogLogCellMeshBound A := mul_one _





/-! ## The finite one-dimensional quadrature defect -/





























end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveMovingSimplexCellIdentification -/
section


/-!
# Exact finite-cell identification for the moving simplex

This file identifies the two-coordinate cell telescope with the literal
difference between the right-corner sampled product and the iterated real
cell integral.  The proof inserts one hybrid product.  All rearrangements
are finite-sum identities or Fubini on one compact cell rectangle; the
joint kernel is measurable and bounded there.

The same real kernel is also prepared in three coordinates.  It is the
literal physical-variable form of the logarithmic moving-simplex density.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## Real moving-simplex kernels -/













theorem fourFiveRealMovingSimplexKernelTwo_nonneg_le_one
    {A y : Nat} {u x z : Real} :
    0 <= fourFiveRealMovingSimplexKernelTwo A y u x z ∧
      fourFiveRealMovingSimplexKernelTwo A y u x z <= 1 := by
  unfold fourFiveRealMovingSimplexKernelTwo
  split_ifs with h
  · have hden : 1 < u - fourFiveRealLogCoordinate y x -
        fourFiveRealLogCoordinate y z := by
      linarith [h.2.2]
    constructor
    · exact inv_nonneg.mpr (zero_le_one.trans hden.le)
    · simpa only [inv_one] using
        (inv_le_inv₀ (zero_lt_one.trans hden) zero_lt_one).mpr hden.le
  · exact ⟨le_rfl, zero_le_one⟩

theorem measurable_fourFiveRealMovingSimplexKernelTwo
    (A y : Nat) (u : Real) :
    Measurable (Function.uncurry
      (fourFiveRealMovingSimplexKernelTwo A y u)) := by
  have hcoordX : Measurable
      (fun p : Real × Real => fourFiveRealLogCoordinate y p.1) :=
    (measurable_fourFiveRealLogCoordinate y).comp measurable_fst
  have hcoordZ : Measurable
      (fun p : Real × Real => fourFiveRealLogCoordinate y p.2) :=
    (measurable_fourFiveRealLogCoordinate y).comp measurable_snd
  have hactive : MeasurableSet {p : Real × Real |
      (A : Real) < p.1 ∧ (A : Real) < p.2 ∧
        fourFiveRealLogCoordinate y p.1 +
          fourFiveRealLogCoordinate y p.2 < u - 1} :=
    (measurable_fst measurableSet_Ioi).inter
      ((measurable_snd measurableSet_Ioi).inter
        ((hcoordX.add hcoordZ) measurableSet_Iio))
  have hrecip : Measurable (fun p : Real × Real =>
      (u - fourFiveRealLogCoordinate y p.1 -
        fourFiveRealLogCoordinate y p.2)⁻¹) :=
    ((measurable_const.sub hcoordX).sub hcoordZ).inv
  unfold Function.uncurry fourFiveRealMovingSimplexKernelTwo
  exact Measurable.ite hactive hrecip measurable_const

theorem fourFiveRealMovingSimplexKernelThree_eq_face_third
    {A y : Nat} {u x z w : Real}
    (hxA : (A : Real) < x) (hzA : (A : Real) < z) :
    fourFiveRealMovingSimplexKernelThree A y u x z w =
      fourFiveRealMovingFaceKernel A y u
        (fourFiveRealLogCoordinate y x +
          fourFiveRealLogCoordinate y z) w := by
  unfold fourFiveRealMovingSimplexKernelThree
    fourFiveRealMovingFaceKernel fourFiveRealMovingFaceReciprocal
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith



/-- The analogous two-coordinate reduction with the first coordinate held
fixed.  This orientation is the one used for the inner `z,w` cell block in
the exact three-dimensional Fubini argument. -/
theorem fourFiveRealMovingSimplexKernelThree_eq_two_shift_first
    {A y : Nat} {u x z w : Real} (hxA : (A : Real) < x) :
    fourFiveRealMovingSimplexKernelThree A y u x z w =
      fourFiveRealMovingSimplexKernelTwo A y
        (u - fourFiveRealLogCoordinate y x) z w := by
  unfold fourFiveRealMovingSimplexKernelThree
    fourFiveRealMovingSimplexKernelTwo
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith











/-! ## Integrability on one literal cell rectangle -/



private theorem integrable_fourFiveRealMovingSimplexDensityTwo_cell
    {A Y y p q : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y) :
    let mu := volume.restrict
      (Set.Ioc (((p - 1 : Nat) : Real)) (p : Real))
    let nu := volume.restrict
      (Set.Ioc (((q - 1 : Nat) : Real)) (q : Real))
    Integrable (fourFiveRealMovingSimplexDensityTwo A y u) (mu.prod nu) := by
  dsimp only
  let mu : Measure Real := volume.restrict
    (Set.Ioc (((p - 1 : Nat) : Real)) (p : Real))
  let nu : Measure Real := volume.restrict
    (Set.Ioc (((q - 1 : Nat) : Real)) (q : Real))
  let delta := fourFiveLogLogCellMeshBound A
  have hA : 2 <= A := hy.trans hyA
  have hdelta : 0 <= delta := (fourFiveLogLogCellMeshBound_pos hA).le
  have hmeas : Measurable
      (fourFiveRealMovingSimplexDensityTwo A y u) := by
    unfold fourFiveRealMovingSimplexDensityTwo
    exact ((measurable_fourFiveLogLogLebesgueDensity.comp measurable_fst).mul
      (measurable_fourFiveLogLogLebesgueDensity.comp measurable_snd)).mul
        (measurable_fourFiveRealMovingSimplexKernelTwo A y u)
  have hconst : Integrable (fun _ : Real × Real => delta ^ 2)
      (mu.prod nu) := integrable_const _
  have hbound : ∀ᵐ r ∂(mu.prod nu),
      ‖fourFiveRealMovingSimplexDensityTwo A y u r‖ <= delta ^ 2 := by
    rw [Measure.ae_prod_iff_ae_ae
      (measurableSet_le hmeas.norm measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    have hdx := fourFiveLogLogLebesgueDensity_le_meshBound hA
      (Finset.mem_Ioc.mp hp).1 (Set.Ioc_subset_Icc_self hx)
    have hdz := fourFiveLogLogLebesgueDensity_le_meshBound hA
      (Finset.mem_Ioc.mp hq).1 (Set.Ioc_subset_Icc_self hz)
    have hK := fourFiveRealMovingSimplexKernelTwo_nonneg_le_one
      (A := A) (y := y) (u := u) (x := x) (z := z)
    rw [fourFiveRealMovingSimplexDensityTwo, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_of_nonneg hdx.1, abs_of_nonneg hdz.1,
      abs_of_nonneg hK.1, pow_two]
    exact calc
      fourFiveLogLogLebesgueDensity x *
          fourFiveLogLogLebesgueDensity z *
            fourFiveRealMovingSimplexKernelTwo A y u x z <=
        delta * delta * 1 := by
          exact mul_le_mul
            (mul_le_mul hdx.2 hdz.2 hdz.1 hdelta)
            hK.2 hK.1 (mul_nonneg hdelta hdelta)
      _ = delta * delta := mul_one _
  exact hconst.mono' hmeas.aestronglyMeasurable hbound

private theorem intervalIntegrable_fourFiveRealMovingSimplexTwo_partial_cell
    {A Y y p q : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y) :
    IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            fourFiveRealMovingSimplexKernelTwo A y u x z))
      volume (((p - 1 : Nat) : Real)) (p : Real) := by
  have hporder : (((p - 1 : Nat) : Real)) <= (p : Real) := by
    exact_mod_cast Nat.sub_le p 1
  have hqorder : (((q - 1 : Nat) : Real)) <= (q : Real) := by
    exact_mod_cast Nat.sub_le q 1
  let mu : Measure Real := volume.restrict
    (Set.Ioc (((p - 1 : Nat) : Real)) (p : Real))
  let nu : Measure Real := volume.restrict
    (Set.Ioc (((q - 1 : Nat) : Real)) (q : Real))
  have hjoint := integrable_fourFiveRealMovingSimplexDensityTwo_cell
    (u := u) hy hyA hp hq
  have hpartial := hjoint.integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hporder]
  simpa [mu, nu, intervalIntegral.integral_of_le hqorder,
    fourFiveRealMovingSimplexDensityTwo,
    MeasureTheory.integral_const_mul, mul_assoc] using hpartial

/-! ## Sample, hybrid, and fully integrated two-coordinate products -/















/-! ## Three coordinates, using the exact two-coordinate block -/











theorem fourFiveRealMovingSimplexKernelThree_nonneg_le_one
    {A y : Nat} {u x z w : Real} :
    0 <= fourFiveRealMovingSimplexKernelThree A y u x z w ∧
      fourFiveRealMovingSimplexKernelThree A y u x z w <= 1 := by
  unfold fourFiveRealMovingSimplexKernelThree
  split_ifs with h
  · have hden : 1 < u - fourFiveRealLogCoordinate y x -
        fourFiveRealLogCoordinate y z - fourFiveRealLogCoordinate y w := by
      linarith [h.2.2.2]
    constructor
    · exact inv_nonneg.mpr (zero_le_one.trans hden.le)
    · simpa only [inv_one] using
        (inv_le_inv₀ (zero_lt_one.trans hden) zero_lt_one).mpr hden.le
  · exact ⟨le_rfl, zero_le_one⟩

theorem measurable_fourFiveRealMovingSimplexKernelThree
    (A y : Nat) (u : Real) :
    Measurable (fun p : (Real × Real) × Real =>
      fourFiveRealMovingSimplexKernelThree A y u p.1.1 p.1.2 p.2) := by
  have hx : Measurable (fun p : (Real × Real) × Real =>
      fourFiveRealLogCoordinate y p.1.1) :=
    (measurable_fourFiveRealLogCoordinate y).comp
      (measurable_fst.comp measurable_fst)
  have hz : Measurable (fun p : (Real × Real) × Real =>
      fourFiveRealLogCoordinate y p.1.2) :=
    (measurable_fourFiveRealLogCoordinate y).comp
      (measurable_snd.comp measurable_fst)
  have hw : Measurable (fun p : (Real × Real) × Real =>
      fourFiveRealLogCoordinate y p.2) :=
    (measurable_fourFiveRealLogCoordinate y).comp measurable_snd
  have hactive : MeasurableSet {p : (Real × Real) × Real |
      (A : Real) < p.1.1 ∧ (A : Real) < p.1.2 ∧
        (A : Real) < p.2 ∧
        fourFiveRealLogCoordinate y p.1.1 +
          fourFiveRealLogCoordinate y p.1.2 +
            fourFiveRealLogCoordinate y p.2 < u - 1} :=
    ((measurable_fst.comp measurable_fst) measurableSet_Ioi).inter
      (((measurable_snd.comp measurable_fst) measurableSet_Ioi).inter
        ((measurable_snd measurableSet_Ioi).inter
          (((hx.add hz).add hw) measurableSet_Iio)))
  have hrecip : Measurable (fun p : (Real × Real) × Real =>
      (u - fourFiveRealLogCoordinate y p.1.1 -
        fourFiveRealLogCoordinate y p.1.2 -
          fourFiveRealLogCoordinate y p.2)⁻¹) :=
    (((measurable_const.sub hx).sub hz).sub hw).inv
  unfold fourFiveRealMovingSimplexKernelThree
  exact Measurable.ite hactive hrecip measurable_const



private theorem integrable_fourFiveRealMovingSimplexDensityThree_cell
    {A Y y p q r : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y) :
    let mu := volume.restrict
      (Set.Ioc (((p - 1 : Nat) : Real)) (p : Real))
    let nu := volume.restrict
      (Set.Ioc (((q - 1 : Nat) : Real)) (q : Real))
    let xi := volume.restrict
      (Set.Ioc (((r - 1 : Nat) : Real)) (r : Real))
    Integrable (fourFiveRealMovingSimplexDensityThree A y u)
      ((mu.prod nu).prod xi) := by
  dsimp only
  let mu : Measure Real := volume.restrict
    (Set.Ioc (((p - 1 : Nat) : Real)) (p : Real))
  let nu : Measure Real := volume.restrict
    (Set.Ioc (((q - 1 : Nat) : Real)) (q : Real))
  let xi : Measure Real := volume.restrict
    (Set.Ioc (((r - 1 : Nat) : Real)) (r : Real))
  let delta := fourFiveLogLogCellMeshBound A
  have hA : 2 <= A := hy.trans hyA
  have hdelta : 0 <= delta := (fourFiveLogLogCellMeshBound_pos hA).le
  have hmeas : Measurable
      (fourFiveRealMovingSimplexDensityThree A y u) := by
    unfold fourFiveRealMovingSimplexDensityThree
    exact (((measurable_fourFiveLogLogLebesgueDensity.comp
      (measurable_fst.comp measurable_fst)).mul
        (measurable_fourFiveLogLogLebesgueDensity.comp
          (measurable_snd.comp measurable_fst))).mul
            (measurable_fourFiveLogLogLebesgueDensity.comp measurable_snd)).mul
      (measurable_fourFiveRealMovingSimplexKernelThree A y u)
  have hconst : Integrable
      (fun _ : (Real × Real) × Real => delta ^ 3)
      ((mu.prod nu).prod xi) := integrable_const _
  have hbound : ∀ᵐ s ∂((mu.prod nu).prod xi),
      ‖fourFiveRealMovingSimplexDensityThree A y u s‖ <= delta ^ 3 := by
    simp only [mu, nu, xi, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem
      ((measurableSet_Ioc.prod measurableSet_Ioc).prod measurableSet_Ioc)]
      with s hs
    rcases s with ⟨⟨x, z⟩, w⟩
    rcases hs with ⟨⟨hx, hz⟩, hw⟩
    have hdx := fourFiveLogLogLebesgueDensity_le_meshBound hA
      (Finset.mem_Ioc.mp hp).1 (Set.Ioc_subset_Icc_self hx)
    have hdz := fourFiveLogLogLebesgueDensity_le_meshBound hA
      (Finset.mem_Ioc.mp hq).1 (Set.Ioc_subset_Icc_self hz)
    have hdw := fourFiveLogLogLebesgueDensity_le_meshBound hA
      (Finset.mem_Ioc.mp hr).1 (Set.Ioc_subset_Icc_self hw)
    have hK := fourFiveRealMovingSimplexKernelThree_nonneg_le_one
      (A := A) (y := y) (u := u) (x := x) (z := z) (w := w)
    rw [fourFiveRealMovingSimplexDensityThree, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_mul, abs_of_nonneg hdx.1,
      abs_of_nonneg hdz.1, abs_of_nonneg hdw.1,
      abs_of_nonneg hK.1, pow_succ, pow_two]
    have hxyz :
        fourFiveLogLogLebesgueDensity x *
            fourFiveLogLogLebesgueDensity z *
              fourFiveLogLogLebesgueDensity w <=
          delta * delta * delta :=
      mul_le_mul
        (mul_le_mul hdx.2 hdz.2 hdz.1 hdelta)
        hdw.2 hdw.1 (mul_nonneg hdelta hdelta)
    have hall :
        fourFiveLogLogLebesgueDensity x *
              fourFiveLogLogLebesgueDensity z *
                fourFiveLogLogLebesgueDensity w *
            fourFiveRealMovingSimplexKernelThree A y u x z w <=
          (delta * delta * delta) * 1 :=
      mul_le_mul hxyz hK.2 hK.1
        (mul_nonneg (mul_nonneg hdelta hdelta) hdelta)
    simpa only [mul_one] using hall
  exact hconst.mono' hmeas.aestronglyMeasurable hbound

private theorem intervalIntegrable_fourFiveRealMovingSimplexThree_partial_cell
    {A Y y p q r : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y) :
    IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)))
      volume (((p - 1 : Nat) : Real)) (p : Real) := by
  have hporder : (((p - 1 : Nat) : Real)) <= (p : Real) := by
    exact_mod_cast Nat.sub_le p 1
  have hqorder : (((q - 1 : Nat) : Real)) <= (q : Real) := by
    exact_mod_cast Nat.sub_le q 1
  have hrorder : (((r - 1 : Nat) : Real)) <= (r : Real) := by
    exact_mod_cast Nat.sub_le r 1
  let mu : Measure Real := volume.restrict
    (Set.Ioc (((p - 1 : Nat) : Real)) (p : Real))
  let nu : Measure Real := volume.restrict
    (Set.Ioc (((q - 1 : Nat) : Real)) (q : Real))
  let xi : Measure Real := volume.restrict
    (Set.Ioc (((r - 1 : Nat) : Real)) (r : Real))
  have hjoint := integrable_fourFiveRealMovingSimplexDensityThree_cell
    (u := u) hy hyA hp hq hr
  have hpartialXZ := hjoint.integral_prod_left
  have hpartialX := hpartialXZ.integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hporder]
  simpa [mu, nu, xi, intervalIntegral.integral_of_le hqorder,
    intervalIntegral.integral_of_le hrorder,
    fourFiveRealMovingSimplexDensityThree,
    MeasureTheory.integral_const_mul, mul_assoc] using hpartialX







private theorem intervalIntegrable_fourFiveThree_lastCellReal_inner
    {A Y y p q r : Nat} {u x : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y)
    (hx : x ∈ Set.uIoc (((p - 1 : Nat) : Real)) (p : Real)) :
    IntervalIntegrable
      (fun z : Real => fourFiveLogLogLebesgueDensity z *
        (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
          fourFiveLogLogLebesgueDensity w *
            fourFiveRealMovingSimplexKernelThree A y u x z w))
      volume (((q - 1 : Nat) : Real)) (q : Real) := by
  have hporder : (((p - 1 : Nat) : Real)) <= (p : Real) := by
    exact_mod_cast Nat.sub_le p 1
  have hxIoc : x ∈ Set.Ioc (((p - 1 : Nat) : Real)) (p : Real) := by
    simpa [Set.uIoc_of_le hporder] using hx
  have hApred : A <= p - 1 := by
    have := (Finset.mem_Ioc.mp hp).1
    omega
  have hxA : (A : Real) < x :=
    (by exact_mod_cast hApred :
      (A : Real) <= ((p - 1 : Nat) : Real)).trans_lt hxIoc.1
  have hright :=
    intervalIntegrable_fourFiveRealMovingSimplexTwo_partial_cell
      (u := u - fourFiveRealLogCoordinate y x) hy hyA hq hr
  apply hright.congr
  intro z _hz
  apply congrArg (fun v : Real => fourFiveLogLogLebesgueDensity z * v)
  apply intervalIntegral.integral_congr
  intro w _hw
  apply congrArg (fun v : Real => fourFiveLogLogLebesgueDensity w * v)
  exact
    (fourFiveRealMovingSimplexKernelThree_eq_two_shift_first
      (A := A) (y := y) (u := u) (x := x) (z := z) (w := w) hxA).symm























/-! ## Exact union of the active physical cells -/

private theorem sum_fourFiveUnitCellIntegrals_eq_interval
    {A Y : Nat} {f : Real -> Real} (hAY : A <= Y)
    (hint : ∀ n ∈ Finset.Ioc A Y,
      IntervalIntegrable f volume
        (((n - 1 : Nat) : Real)) (n : Real)) :
    (∑ n ∈ Finset.Ioc A Y,
        ∫ x in (((n - 1 : Nat) : Real))..(n : Real), f x) =
      ∫ x in (A : Real)..(Y : Real), f x := by
  rw [Erdos390.Full.FriableAsymptotic.sum_Ioc_shift]
  have h := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (f := f) (μ := volume) (a := fun k : Nat => (k : Real)) hAY
    (fun k hk => by
      have hn : k + 1 ∈ Finset.Ioc A Y := by
        simpa [Finset.mem_Ico, Finset.mem_Ioc] using hk
      simpa [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using
        hint (k + 1) hn)
  simpa [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using h













private theorem fourFiveThree_inner_cell_union
    {A Y y p q : Nat} {u x z : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hx : x ∈ Set.uIoc (((p - 1 : Nat) : Real)) (p : Real))
    (hz : z ∈ Set.uIoc (((q - 1 : Nat) : Real)) (q : Real)) :
    (∑ r ∈ Finset.Ioc A Y,
        ∫ w in (((r - 1 : Nat) : Real))..(r : Real),
          fourFiveLogLogLebesgueDensity w *
            fourFiveRealMovingSimplexKernelThree A y u x z w) =
      ∫ w in (A : Real)..(Y : Real),
        fourFiveLogLogLebesgueDensity w *
          fourFiveRealMovingSimplexKernelThree A y u x z w := by
  have hxIoc : x ∈ Set.Ioc (((p - 1 : Nat) : Real)) (p : Real) := by
    simpa [Set.uIoc_of_le
      (by exact_mod_cast Nat.sub_le p 1)] using hx
  have hzIoc : z ∈ Set.Ioc (((q - 1 : Nat) : Real)) (q : Real) := by
    simpa [Set.uIoc_of_le
      (by exact_mod_cast Nat.sub_le q 1)] using hz
  have hxA : (A : Real) < x := by
    have hAp : A <= p - 1 := by
      have := (Finset.mem_Ioc.mp hp).1
      omega
    exact (by exact_mod_cast hAp :
      (A : Real) <= ((p - 1 : Nat) : Real)).trans_lt hxIoc.1
  have hzA : (A : Real) < z := by
    have hAq : A <= q - 1 := by
      have := (Finset.mem_Ioc.mp hq).1
      omega
    exact (by exact_mod_cast hAq :
      (A : Real) <= ((q - 1 : Nat) : Real)).trans_lt hzIoc.1
  apply sum_fourFiveUnitCellIntegrals_eq_interval hAY
  intro r hr
  have hface := intervalIntegrable_fourFiveDensity_mul_realMovingFace_cell
    (u := u) (c := fourFiveRealLogCoordinate y x +
      fourFiveRealLogCoordinate y z) hy hyA hr
  apply hface.congr
  intro w _hw
  exact congrArg (fun v : Real => fourFiveLogLogLebesgueDensity w * v)
    (fourFiveRealMovingSimplexKernelThree_eq_face_third
      (A := A) (y := y) (u := u) (x := x) (z := z) (w := w)
        hxA hzA).symm

private theorem fourFiveThree_sum_lastRealCells_inside_middle
    {A Y y p q : Nat} {u x : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hx : x ∈ Set.uIoc (((p - 1 : Nat) : Real)) (p : Real)) :
    (∑ r ∈ Finset.Ioc A Y,
        ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)) =
      ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
        fourFiveLogLogLebesgueDensity z *
          (∫ w in (A : Real)..(Y : Real),
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree A y u x z w) := by
  calc
    (∑ r ∈ Finset.Ioc A Y,
        ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)) =
      ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
        ∑ r ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w) := by
          symm
          exact intervalIntegral.integral_finset_sum
            (fun r hr => intervalIntegrable_fourFiveThree_lastCellReal_inner
              hy hyA hp hq hr hx)
    _ = ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
        fourFiveLogLogLebesgueDensity z *
          (∫ w in (A : Real)..(Y : Real),
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree A y u x z w) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with z
      intro hz
      rw [← Finset.mul_sum]
      apply congrArg (fun v : Real => fourFiveLogLogLebesgueDensity z * v)
      exact fourFiveThree_inner_cell_union hy hyA hAY hp hq hx hz

private theorem intervalIntegrable_fourFiveThree_middle_with_activeLast
    {A Y y p q : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y) :
    IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (A : Real)..(Y : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)))
      volume (((p - 1 : Nat) : Real)) (p : Real) := by
  have hsum : IntervalIntegrable
      (∑ r ∈ Finset.Ioc A Y,
        fun x : Real => fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree A y u x z w)))
      volume (((p - 1 : Nat) : Real)) (p : Real) :=
    IntervalIntegrable.sum (Finset.Ioc A Y)
      (fun r hr =>
        intervalIntegrable_fourFiveRealMovingSimplexThree_partial_cell
          (u := u) hy hyA hp hq hr)
  apply hsum.congr
  intro x hx
  rw [Finset.sum_apply]
  calc
    (∑ r ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree A y u x z w))) =
      fourFiveLogLogLebesgueDensity x *
        (∑ r ∈ Finset.Ioc A Y,
          ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree A y u x z w)) := by
        rw [Finset.mul_sum]
    _ = fourFiveLogLogLebesgueDensity x *
        (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (A : Real)..(Y : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)) :=
      congrArg (fun v : Real => fourFiveLogLogLebesgueDensity x * v)
        (fourFiveThree_sum_lastRealCells_inside_middle
          (u := u) hy hyA hAY hp hq hx)

private theorem fourFiveThree_middle_cell_union
    {A Y y p : Nat} {u x : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hp : p ∈ Finset.Ioc A Y)
    (hx : x ∈ Set.uIoc (((p - 1 : Nat) : Real)) (p : Real)) :
    (∑ q ∈ Finset.Ioc A Y,
        ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (A : Real)..(Y : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)) =
      ∫ z in (A : Real)..(Y : Real),
        fourFiveLogLogLebesgueDensity z *
          (∫ w in (A : Real)..(Y : Real),
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree A y u x z w) := by
  apply sum_fourFiveUnitCellIntegrals_eq_interval hAY
  intro q hq
  have hsum : IntervalIntegrable
      (∑ r ∈ Finset.Ioc A Y,
        fun z : Real => fourFiveLogLogLebesgueDensity z *
          (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree A y u x z w))
      volume (((q - 1 : Nat) : Real)) (q : Real) :=
    IntervalIntegrable.sum (Finset.Ioc A Y)
      (fun r hr => intervalIntegrable_fourFiveThree_lastCellReal_inner
        hy hyA hp hq hr hx)
  apply hsum.congr
  intro z hz
  rw [Finset.sum_apply]
  calc
    (∑ r ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueDensity z *
          (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree A y u x z w)) =
      fourFiveLogLogLebesgueDensity z *
        (∑ r ∈ Finset.Ioc A Y,
          ∫ w in (((r - 1 : Nat) : Real))..(r : Real),
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree A y u x z w) := by
        rw [Finset.mul_sum]
    _ = fourFiveLogLogLebesgueDensity z *
        (∫ w in (A : Real)..(Y : Real),
          fourFiveLogLogLebesgueDensity w *
            fourFiveRealMovingSimplexKernelThree A y u x z w) :=
      congrArg (fun v : Real => fourFiveLogLogLebesgueDensity z * v)
        (fourFiveThree_inner_cell_union (u := u)
          hy hyA hAY hp hq hx hz)

private theorem intervalIntegrable_fourFiveThree_active_union_cell
    {A Y y p : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hp : p ∈ Finset.Ioc A Y) :
    IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        (∫ z in (A : Real)..(Y : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (A : Real)..(Y : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)))
      volume (((p - 1 : Nat) : Real)) (p : Real) := by
  have hsum : IntervalIntegrable
      (∑ q ∈ Finset.Ioc A Y,
        fun x : Real => fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              (∫ w in (A : Real)..(Y : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree A y u x z w)))
      volume (((p - 1 : Nat) : Real)) (p : Real) :=
    IntervalIntegrable.sum (Finset.Ioc A Y)
      (fun q hq => intervalIntegrable_fourFiveThree_middle_with_activeLast
        hy hyA hAY hp hq)
  apply hsum.congr
  intro x hx
  rw [Finset.sum_apply]
  calc
    (∑ q ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              (∫ w in (A : Real)..(Y : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree A y u x z w))) =
      fourFiveLogLogLebesgueDensity x *
        (∑ q ∈ Finset.Ioc A Y,
          ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              (∫ w in (A : Real)..(Y : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree A y u x z w)) := by
        rw [Finset.mul_sum]
    _ = fourFiveLogLogLebesgueDensity x *
        (∫ z in (A : Real)..(Y : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (A : Real)..(Y : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)) :=
      congrArg (fun v : Real => fourFiveLogLogLebesgueDensity x * v)
        (fourFiveThree_middle_cell_union (u := u) hy hyA hAY hp hx)

/-- Exact three-dimensional adjacent-cell union. -/
theorem fourFiveMovingSimplexIteratedRealCellProductThree_eq_activePhysical
    {A Y y : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y) :
    fourFiveMovingSimplexIteratedRealCellProductThree A Y y u =
      fourFiveMovingSimplexActivePhysicalIntegralThree A Y y u := by
  unfold fourFiveMovingSimplexIteratedRealCellProductThree
    fourFiveMovingSimplexActivePhysicalIntegralThree
  calc
    (∑ p ∈ Finset.Ioc A Y,
        ∑ q ∈ Finset.Ioc A Y,
          ∑ r ∈ Finset.Ioc A Y,
            ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
              fourFiveLogLogLebesgueDensity x *
                (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                  fourFiveLogLogLebesgueDensity z *
                    (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                      fourFiveLogLogLebesgueDensity w *
                        fourFiveRealMovingSimplexKernelThree A y u x z w))) =
      ∑ p ∈ Finset.Ioc A Y,
        ∑ q ∈ Finset.Ioc A Y,
          ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
            ∑ r ∈ Finset.Ioc A Y,
              fourFiveLogLogLebesgueDensity x *
                (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                  fourFiveLogLogLebesgueDensity z *
                    (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                      fourFiveLogLogLebesgueDensity w *
                        fourFiveRealMovingSimplexKernelThree A y u x z w)) := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          symm
          exact intervalIntegral.integral_finset_sum
            (fun r hr =>
              intervalIntegrable_fourFiveRealMovingSimplexThree_partial_cell
                (u := u) hy hyA hp hq hr)
    _ = ∑ p ∈ Finset.Ioc A Y,
        ∑ q ∈ Finset.Ioc A Y,
          ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  (∫ w in (A : Real)..(Y : Real),
                    fourFiveLogLogLebesgueDensity w *
                      fourFiveRealMovingSimplexKernelThree A y u x z w)) := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          apply intervalIntegral.integral_congr_ae
          filter_upwards with x
          intro hx
          rw [← Finset.mul_sum]
          apply congrArg
            (fun v : Real => fourFiveLogLogLebesgueDensity x * v)
          exact fourFiveThree_sum_lastRealCells_inside_middle
            hy hyA hAY hp hq hx
    _ = ∑ p ∈ Finset.Ioc A Y,
        ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          ∑ q ∈ Finset.Ioc A Y,
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  (∫ w in (A : Real)..(Y : Real),
                    fourFiveLogLogLebesgueDensity w *
                      fourFiveRealMovingSimplexKernelThree A y u x z w)) := by
          apply Finset.sum_congr rfl
          intro p hp
          symm
          exact intervalIntegral.integral_finset_sum
            (fun q hq => intervalIntegrable_fourFiveThree_middle_with_activeLast
              hy hyA hAY hp hq)
    _ = ∑ p ∈ Finset.Ioc A Y,
        ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            (∫ z in (A : Real)..(Y : Real),
              fourFiveLogLogLebesgueDensity z *
                (∫ w in (A : Real)..(Y : Real),
                  fourFiveLogLogLebesgueDensity w *
                    fourFiveRealMovingSimplexKernelThree A y u x z w)) := by
          apply Finset.sum_congr rfl
          intro p hp
          apply intervalIntegral.integral_congr_ae
          filter_upwards with x
          intro hx
          rw [← Finset.mul_sum]
          apply congrArg
            (fun v : Real => fourFiveLogLogLebesgueDensity x * v)
          exact fourFiveThree_middle_cell_union hy hyA hAY hp hx
    _ = ∫ x in (A : Real)..(Y : Real),
        fourFiveLogLogLebesgueDensity x *
          (∫ z in (A : Real)..(Y : Real),
            fourFiveLogLogLebesgueDensity z *
              (∫ w in (A : Real)..(Y : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree A y u x z w)) :=
      sum_fourFiveUnitCellIntegrals_eq_interval hAY
        (fun p hp => intervalIntegrable_fourFiveThree_active_union_cell
          hy hyA hAY hp)

/-! ## Joint integrability on the finite active box -/







end Erdos390.WholePaper.BankPaperRealization

end

theorem solution :
∀ {A Y y : Nat} {u : Real},
  LE.le.{0} (2 : Nat) y →
    LE.le.{0} y A →
      LE.le.{0} A Y →
        Eq.{1} (Erdos390.WholePaper.BankPaperRealization.fourFiveMovingSimplexIteratedRealCellProductThree A Y y u)
          (Erdos390.WholePaper.BankPaperRealization.fourFiveMovingSimplexActivePhysicalIntegralThree A Y y u) := by
  exact @Erdos390.WholePaper.BankPaperRealization.fourFiveMovingSimplexIteratedRealCellProductThree_eq_activePhysical
