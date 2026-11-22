-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.fourFiveMovingSimplexHybridCellProductTwo_sub_iterated
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:53:56.442426+00:00
-- url     : https://prove2.me/submissions/a5496510-d474-44c1-866e-e703c143f72a

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_009

/- Source module: Erdos390.WholePaper.BankPaperFourFiveCellLebesgueIdentification -/
section


/-!
# Log-log cells as literal Lebesgue cells

The continuum atom used by the reciprocal-prime BV transfer is not a
formal surrogate: on every integer cell `(m-1,m]` it is exactly the
Lebesgue integral of `dx / (x log x)`.  This file proves that identity and
rewrites the one-, two-, and three-coordinate cell products as products of
literal Lebesgue cell integrals.

The endpoint convention is immaterial for these absolutely continuous
cell measures.  No limiting argument is used in this identification.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory





theorem continuousOn_fourFiveLogLogLebesgueDensity
    {a b : Real} (ha : 1 < a) :
    ContinuousOn fourFiveLogLogLebesgueDensity (Set.Icc a b) := by
  intro x hx
  have hx1 : 1 < x := ha.trans_le hx.1
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  unfold fourFiveLogLogLebesgueDensity
  exact ContinuousAt.continuousWithinAt
    (continuousAt_const.div
      (continuousAt_id.mul (Real.continuousAt_log hx0))
      (mul_ne_zero hx0 hlog0))























end Erdos390.WholePaper.BankPaperRealization

end

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

theorem fourFiveRealMovingFaceKernel_natCast
    {A y n : Nat} {u c : Real} :
    fourFiveRealMovingFaceKernel A y u c (n : Real) =
      fourFiveMovingFaceKernel A y u c n := by
  unfold fourFiveRealMovingFaceKernel fourFiveMovingFaceKernel
    fourFiveRealMovingFaceReciprocal
  by_cases hAn : A < n
  · have hcast : (A : Real) < (n : Real) := by exact_mod_cast hAn
    simp [hAn, hcast]
  · have hcast : ¬(A : Real) < (n : Real) := by exact_mod_cast hAn
    simp [hAn, hcast]

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



/-- On every paper cell, the signed integral above is exactly the
right-endpoint mass times the sampled kernel minus the varying real-kernel
integral. -/
theorem fourFiveLebesgueCell_sample_sub_real_eq_defect
    {A Y y n : Nat} {u c : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hn : n ∈ Finset.Ioc A Y) :
    fourFiveLogLogLebesgueCellAtom n *
          fourFiveMovingFaceKernel A y u c n -
        (∫ x in (((n - 1 : Nat) : Real))..(n : Real),
          fourFiveLogLogLebesgueDensity x *
            fourFiveRealMovingFaceKernel A y u c x) =
      fourFiveMovingFaceLebesgueCellDefect A Y y u c n := by
  have hleft : (1 : Real) < ((n - 1 : Nat) : Real) := by
    exact_mod_cast (show 1 < n - 1 by
      have hnA := (Finset.mem_Ioc.mp hn).1
      omega)
  have hab : (((n - 1 : Nat) : Real)) <= (n : Real) := by
    exact_mod_cast Nat.sub_le n 1
  have hdensity : IntervalIntegrable fourFiveLogLogLebesgueDensity
      volume (((n - 1 : Nat) : Real)) (n : Real) :=
    (continuousOn_fourFiveLogLogLebesgueDensity hleft)
      |>.intervalIntegrable_of_Icc hab
  have hsample : IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        fourFiveMovingFaceKernel A y u c n)
      volume (((n - 1 : Nat) : Real)) (n : Real) :=
    hdensity.mul_const _
  have hreal :=
    intervalIntegrable_fourFiveDensity_mul_realMovingFace_cell
      (u := u) (c := c) hy hyA hn
  unfold fourFiveLogLogLebesgueCellAtom
    fourFiveMovingFaceLebesgueCellDefect
  rw [← intervalIntegral.integral_mul_const,
    ← intervalIntegral.integral_sub hsample hreal]
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

























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







theorem fourFiveRealMovingSimplexKernelTwo_eq_face_first
    {A y : Nat} {u x z : Real} (hzA : (A : Real) < z) :
    fourFiveRealMovingSimplexKernelTwo A y u x z =
      fourFiveRealMovingFaceKernel A y u
        (fourFiveRealLogCoordinate y z) x := by
  unfold fourFiveRealMovingSimplexKernelTwo
    fourFiveRealMovingFaceKernel fourFiveRealMovingFaceReciprocal
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith

theorem fourFiveRealMovingSimplexKernelTwo_eq_face_second
    {A y : Nat} {u x z : Real} (hxA : (A : Real) < x) :
    fourFiveRealMovingSimplexKernelTwo A y u x z =
      fourFiveRealMovingFaceKernel A y u
        (fourFiveRealLogCoordinate y x) z := by
  unfold fourFiveRealMovingSimplexKernelTwo
    fourFiveRealMovingFaceKernel fourFiveRealMovingFaceReciprocal
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith



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









theorem fourFiveMovingSimplexHybridCellProductTwo_sub_iterated
    {A Y y : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) :
    fourFiveMovingSimplexHybridCellProductTwo A Y y u -
        fourFiveMovingSimplexIteratedRealCellProductTwo A Y y u =
      ∑ p ∈ Finset.Ioc A Y,
        ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            fourFiveMovingFaceLebesgueCellDefectSum A Y y u
              (fourFiveRealLogCoordinate y x) := by
  unfold fourFiveMovingSimplexHybridCellProductTwo
    fourFiveMovingSimplexIteratedRealCellProductTwo
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hpA : ∀ x ∈ Set.uIoc (((p - 1 : Nat) : Real)) (p : Real),
      (A : Real) < x := by
    intro x hx
    have hporder : (((p - 1 : Nat) : Real)) <= (p : Real) := by
      exact_mod_cast Nat.sub_le p 1
    have hxIoc :
        x ∈ Set.Ioc (((p - 1 : Nat) : Real)) (p : Real) := by
      simpa only [Set.uIoc_of_le hporder] using hx
    have hApred : A <= p - 1 := by
      have := (Finset.mem_Ioc.mp hp).1
      omega
    exact (by exact_mod_cast hApred :
      (A : Real) <= ((p - 1 : Nat) : Real)).trans_lt hxIoc.1
  have hleftIntegrable (q : Nat) (hq : q ∈ Finset.Ioc A Y) :
      IntervalIntegrable
        (fun x : Real => fourFiveLogLogLebesgueDensity x *
          (fourFiveLogLogLebesgueCellAtom q *
            fourFiveRealMovingSimplexKernelTwo A y u x (q : Real)))
        volume (((p - 1 : Nat) : Real)) (p : Real) := by
    have hqA : (A : Real) < (q : Real) := by
      exact_mod_cast (Finset.mem_Ioc.mp hq).1
    have hbase := intervalIntegrable_fourFiveDensity_mul_realMovingFace_cell
      (u := u) (c := fourFiveLogCoordinate y q) hy hyA hp
    apply (hbase.const_mul
      (fourFiveLogLogLebesgueCellAtom q)).congr
    intro x hx
    have hreal :
        fourFiveRealMovingSimplexKernelTwo A y u x (q : Real) =
          fourFiveRealMovingFaceKernel A y u
            (fourFiveLogCoordinate y q) x := by
      simpa only [fourFiveRealLogCoordinate_natCast] using
        (fourFiveRealMovingSimplexKernelTwo_eq_face_first
          (A := A) (y := y) (u := u) (x := x)
          (z := (q : Real)) hqA)
    calc
      fourFiveLogLogLebesgueCellAtom q *
            (fourFiveLogLogLebesgueDensity x *
              fourFiveRealMovingFaceKernel A y u
                (fourFiveLogCoordinate y q) x) =
          fourFiveLogLogLebesgueDensity x *
            (fourFiveLogLogLebesgueCellAtom q *
              fourFiveRealMovingFaceKernel A y u
                (fourFiveLogCoordinate y q) x) := by
        ring
      _ = fourFiveLogLogLebesgueDensity x *
            (fourFiveLogLogLebesgueCellAtom q *
              fourFiveRealMovingSimplexKernelTwo A y u
                x (q : Real)) :=
        congrArg
          (fun k : Real => fourFiveLogLogLebesgueDensity x *
            (fourFiveLogLogLebesgueCellAtom q * k))
          hreal.symm
  have hrightIntegrable (q : Nat) (hq : q ∈ Finset.Ioc A Y) :=
    intervalIntegrable_fourFiveRealMovingSimplexTwo_partial_cell
      (u := u) hy hyA hp hq
  have hdiffIntegrable (q : Nat) (hq : q ∈ Finset.Ioc A Y) :
      IntervalIntegrable
        (fun x : Real =>
          fourFiveLogLogLebesgueDensity x *
              (fourFiveLogLogLebesgueCellAtom q *
                fourFiveRealMovingSimplexKernelTwo A y u x (q : Real)) -
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveRealMovingSimplexKernelTwo A y u x z))
        volume (((p - 1 : Nat) : Real)) (p : Real) :=
    (hleftIntegrable q hq).sub (hrightIntegrable q hq)
  calc
    (∑ q ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueCellAtom q *
            (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
              fourFiveLogLogLebesgueDensity x *
                fourFiveRealMovingSimplexKernelTwo A y u x (q : Real))) -
        ∑ q ∈ Finset.Ioc A Y,
          ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveRealMovingSimplexKernelTwo A y u x z) =
      ∑ q ∈ Finset.Ioc A Y,
        ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          (fourFiveLogLogLebesgueDensity x *
              (fourFiveLogLogLebesgueCellAtom q *
                fourFiveRealMovingSimplexKernelTwo A y u x (q : Real)) -
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveRealMovingSimplexKernelTwo A y u x z)) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro q hq
        calc
          fourFiveLogLogLebesgueCellAtom q *
                (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                  fourFiveLogLogLebesgueDensity x *
                    fourFiveRealMovingSimplexKernelTwo A y u x (q : Real)) -
              ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                fourFiveLogLogLebesgueDensity x *
                  (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                    fourFiveLogLogLebesgueDensity z *
                      fourFiveRealMovingSimplexKernelTwo A y u x z) =
            (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                fourFiveLogLogLebesgueDensity x *
                  (fourFiveLogLogLebesgueCellAtom q *
                    fourFiveRealMovingSimplexKernelTwo A y u x (q : Real))) -
              ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                fourFiveLogLogLebesgueDensity x *
                  (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                    fourFiveLogLogLebesgueDensity z *
                      fourFiveRealMovingSimplexKernelTwo A y u x z) := by
              congr 1
              rw [← intervalIntegral.integral_const_mul]
              apply intervalIntegral.integral_congr
              intro x _hx
              ring
          _ = ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
              (fourFiveLogLogLebesgueDensity x *
                  (fourFiveLogLogLebesgueCellAtom q *
                    fourFiveRealMovingSimplexKernelTwo A y u x (q : Real)) -
                fourFiveLogLogLebesgueDensity x *
                  (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                    fourFiveLogLogLebesgueDensity z *
                      fourFiveRealMovingSimplexKernelTwo A y u x z)) :=
            (intervalIntegral.integral_sub
              (hleftIntegrable q hq) (hrightIntegrable q hq)).symm
    _ = ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        ∑ q ∈ Finset.Ioc A Y,
          (fourFiveLogLogLebesgueDensity x *
              (fourFiveLogLogLebesgueCellAtom q *
                fourFiveRealMovingSimplexKernelTwo A y u x (q : Real)) -
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveRealMovingSimplexKernelTwo A y u x z)) := by
      symm
      exact intervalIntegral.integral_finset_sum hdiffIntegrable
    _ = ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        fourFiveLogLogLebesgueDensity x *
          fourFiveMovingFaceLebesgueCellDefectSum A Y y u
            (fourFiveRealLogCoordinate y x) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x
      intro hx
      unfold fourFiveMovingFaceLebesgueCellDefectSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [← mul_sub]
      apply congrArg
        (fun z : Real => fourFiveLogLogLebesgueDensity x * z)
      have hface (z : Real) :
          fourFiveRealMovingSimplexKernelTwo A y u x z =
            fourFiveRealMovingFaceKernel A y u
              (fourFiveRealLogCoordinate y x) z :=
        fourFiveRealMovingSimplexKernelTwo_eq_face_second (hpA x hx)
      have hsample :
          fourFiveRealMovingSimplexKernelTwo A y u x (q : Real) =
            fourFiveMovingFaceKernel A y u
              (fourFiveRealLogCoordinate y x) q := by
        calc
          fourFiveRealMovingSimplexKernelTwo A y u x (q : Real) =
              fourFiveRealMovingFaceKernel A y u
                (fourFiveRealLogCoordinate y x) (q : Real) :=
            hface (q : Real)
          _ = fourFiveMovingFaceKernel A y u
                (fourFiveRealLogCoordinate y x) q :=
            fourFiveRealMovingFaceKernel_natCast
      have hintegral :
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                fourFiveRealMovingSimplexKernelTwo A y u x z) =
            ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                fourFiveRealMovingFaceKernel A y u
                  (fourFiveRealLogCoordinate y x) z := by
        apply intervalIntegral.integral_congr
        intro z _hz
        exact congrArg (fun t : Real =>
          fourFiveLogLogLebesgueDensity z * t) (hface z)
      rw [hsample, hintegral]
      exact fourFiveLebesgueCell_sample_sub_real_eq_defect hy hyA hq





/-! ## Three coordinates, using the exact two-coordinate block -/



















































/-! ## Exact union of the active physical cells -/



























/-! ## Joint integrability on the finite active box -/







end Erdos390.WholePaper.BankPaperRealization

end

theorem solution :
∀ {A Y y : Nat} {u : Real},
  LE.le.{0} (2 : Nat) y →
    LE.le.{0} y A →
      Eq.{1}
        (HSub.hSub.{0, 0, 0}
          (Erdos390.WholePaper.BankPaperRealization.fourFiveMovingSimplexHybridCellProductTwo A Y y u)
          (Erdos390.WholePaper.BankPaperRealization.fourFiveMovingSimplexIteratedRealCellProductTwo A Y y u))
        (∑ p ∈ Finset.Ioc.{0} A Y,
          ∫ (x : Real) in ↑(HSub.hSub.{0, 0, 0} p (1 : Nat))..↑p,
            HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.BankPaperRealization.fourFiveLogLogLebesgueDensity x)
              (Erdos390.WholePaper.BankPaperRealization.fourFiveMovingFaceLebesgueCellDefectSum A Y y u
                (Erdos390.WholePaper.BankPaperRealization.fourFiveRealLogCoordinate y x))) := by
  exact @Erdos390.WholePaper.BankPaperRealization.fourFiveMovingSimplexHybridCellProductTwo_sub_iterated
