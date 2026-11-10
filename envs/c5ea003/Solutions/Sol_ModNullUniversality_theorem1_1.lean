-- Prove2me | solution 1 for ModNullUniversality.theorem1_1
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-11-09T09:52:40.754824+00:00
-- url     : https://prove2.me/submissions/ec28315c-28dd-44e1-a3ed-c609e0b44179

import Definitions.Def_ModNullCompact20261109
import Definitions.Def_ModNullCore20261109
import Definitions.Def_NoBorelUpperBound20261101
import Definitions.Def_NoBorelUpperBoundTransfer20261101
import Definitions.Def_NoUniversalFSigma261031052
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Equiv.List
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.List
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.Polish

-- BEGIN COMPLETE MODULE NoBorelUpperBound.L1Coordinates
section
                                                
                                               
                     

noncomputable section
open Set TopologicalSpace
open scoped BigOperators ENNReal

namespace NoBorelUpperBoundFSigma.L1Coordinates
universe u v

abbrev L1 (I : Type u) := lp (fun _ : I => ℝ) 1
abbrev MatrixL1 (I : Type u) (J : Type v) := L1 (I × J)
variable {I : Type u} {J : Type v}

theorem summable_norm (x : L1 I) : Summable (fun i => ‖x i‖) := by
  simpa using (lp.memℓp x).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)

theorem norm_eq_tsum (x : L1 I) : ‖x‖ = ∑' i, ‖x i‖ := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (1 : ℝ≥0∞).toReal) x

def restrict (e : I → J) (he : Function.Injective e) (x : L1 J) : L1 I :=
  ⟨fun i => x (e i), memℓp_gen (by
    simpa using (summable_norm x).comp_injective he)⟩

@[simp] theorem restrict_apply (e : I → J) (he : Function.Injective e) (x : L1 J) (i : I) :
    restrict e he x i = x (e i) := rfl

theorem norm_restrict_le (e : I → J) (he : Function.Injective e) (x : L1 J) :
    ‖restrict e he x‖ ≤ ‖x‖ := by
  classical
  apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg x)
  intro s
  have hsum : ∑ i ∈ s, ‖x (e i)‖ ^ (1 : ℝ≥0∞).toReal =
      ∑ j ∈ s.image e, ‖x j‖ ^ (1 : ℝ≥0∞).toReal := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => he h
  change ∑ i ∈ s, ‖x (e i)‖ ^ (1 : ℝ≥0∞).toReal ≤ ‖x‖ ^ (1 : ℝ≥0∞).toReal
  rw [hsum]
  exact lp.sum_rpow_le_norm_rpow (by norm_num) x (s.image e)

def restrictCLM (e : I → J) (he : Function.Injective e) : L1 J →L[ℝ] L1 I :=
  ({ toFun := restrict e he
     map_add' := by intro x y; ext i; rfl
     map_smul' := by intro c x; ext i; rfl } : L1 J →ₗ[ℝ] L1 I).mkContinuous 1
    (by intro x; simpa using norm_restrict_le e he x)

@[simp] theorem restrictCLM_apply (e : I → J) (he : Function.Injective e) (x : L1 J) (i : I) :
    restrictCLM e he x i = x (e i) := rfl

def reindex {K : Type*} (e : I ≃ K) : L1 I ≃ₗᵢ[ℝ] L1 K where
  toFun := restrict e.symm e.symm.injective
  invFun := restrict e e.injective
  left_inv x := by ext i; simp
  right_inv x := by ext j; simp
  map_add' x y := by ext j; rfl
  map_smul' a x := by ext j; rfl
  norm_map' x := by
    apply le_antisymm (norm_restrict_le _ _ _)
    have h := norm_restrict_le e e.injective (restrict e.symm e.symm.injective x)
    have he : restrict e e.injective (restrict e.symm e.symm.injective x) = x := by ext i; simp
    rwa [he] at h

@[simp] theorem reindex_apply {K : Type*} (e : I ≃ K) (x : L1 I) (k : K) :
    reindex e x k = x (e.symm k) := rfl

def row (i : I) : MatrixL1 I J →L[ℝ] L1 J :=
  restrictCLM (fun j => (i, j)) (fun _ _ h => (Prod.mk.inj h).2)
def col (j : J) : MatrixL1 I J →L[ℝ] L1 I :=
  restrictCLM (fun i => (i, j)) (fun _ _ h => (Prod.mk.inj h).1)

@[simp] theorem row_apply (i : I) (x : MatrixL1 I J) (j : J) : row i x j = x (i, j) := rfl
@[simp] theorem col_apply (j : J) (x : MatrixL1 I J) (i : I) : col j x i = x (i, j) := rfl

theorem summable_norm_outer (x : L1 I) (y : L1 J) :
    Summable (fun p : I × J => ‖x p.1 * y p.2‖) := by
  simpa only [norm_mul] using
    (summable_norm x).mul_of_nonneg (summable_norm y)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

def outer (x : L1 I) (y : L1 J) : MatrixL1 I J :=
  ⟨fun p => x p.1 * y p.2, memℓp_gen (by simpa using summable_norm_outer x y)⟩

@[simp] theorem outer_apply (x : L1 I) (y : L1 J) (p : I × J) :
    outer x y p = x p.1 * y p.2 := rfl

theorem norm_outer (x : L1 I) (y : L1 J) : ‖outer x y‖ = ‖x‖ * ‖y‖ := by
  rw [norm_eq_tsum, norm_eq_tsum, norm_eq_tsum,
    (summable_norm x).tsum_mul_tsum (summable_norm y)
      ((summable_norm x).mul_of_nonneg (summable_norm y)
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))]
  simp only [outer_apply, norm_mul]

@[simp] theorem outer_zero_left (y : L1 J) : outer (0 : L1 I) y = 0 := by
  ext p; change 0 * y p.2 = 0; exact zero_mul _
@[simp] theorem outer_zero_right (x : L1 I) : outer x (0 : L1 J) = 0 := by
  ext p; change x p.1 * 0 = 0; exact mul_zero _
@[simp] theorem outer_add_left (x x' : L1 I) (y : L1 J) :
    outer (x + x') y = outer x y + outer x' y := by
  ext p; change (x p.1 + x' p.1) * y p.2 = x p.1 * y p.2 + x' p.1 * y p.2; ring
@[simp] theorem outer_add_right (x : L1 I) (y y' : L1 J) :
    outer x (y + y') = outer x y + outer x y' := by
  ext p; change x p.1 * (y p.2 + y' p.2) = x p.1 * y p.2 + x p.1 * y' p.2; ring
@[simp] theorem outer_smul_left (c : ℝ) (x : L1 I) (y : L1 J) :
    outer (c • x) y = c • outer x y := by
  ext p; change (c * x p.1) * y p.2 = c * (x p.1 * y p.2); ring
@[simp] theorem outer_smul_right (c : ℝ) (x : L1 I) (y : L1 J) :
    outer x (c • y) = c • outer x y := by
  ext p; change x p.1 * (c * y p.2) = c * (x p.1 * y p.2); ring

def outerBilinear : L1 I →L[ℝ] L1 J →L[ℝ] MatrixL1 I J :=
  ({ toFun := fun x =>
       { toFun := outer x
         map_add' := outer_add_right x
         map_smul' := by intro c y; exact outer_smul_right c x y }
     map_add' := by intro x x'; apply LinearMap.ext; intro y; exact outer_add_left x x' y
     map_smul' := by intro c x; apply LinearMap.ext; intro y; exact outer_smul_left c x y } :
    L1 I →ₗ[ℝ] L1 J →ₗ[ℝ] MatrixL1 I J).mkContinuous₂ 1
      (by intro x y; simpa using (norm_outer x y).le)

@[simp] theorem outerBilinear_apply (x : L1 I) (y : L1 J) : outerBilinear x y = outer x y := rfl
theorem continuous_outer : Continuous (fun p : L1 I × L1 J => outer p.1 p.2) := by
  simpa only [Function.uncurry_def, outerBilinear_apply] using
    (outerBilinear (I := I) (J := J)).continuous₂

@[simp] theorem row_outer (i : I) (x : L1 I) (y : L1 J) :
    row i (outer x y) = (x i) • y := by ext j; simp
@[simp] theorem col_outer (j : J) (x : L1 I) (y : L1 J) :
    col j (outer x y) = (y j) • x := by ext i; simp [mul_comm]

def transpose : MatrixL1 I J ≃ₗᵢ[ℝ] MatrixL1 J I := reindex (Equiv.prodComm I J)

@[simp] theorem transpose_apply (R : MatrixL1 I J) (j : J) (i : I) :
    transpose R (j,i) = R (i,j) := rfl

@[simp] theorem transpose_outer (x : L1 I) (y : L1 J) : transpose (outer x y) = outer y x := by
  ext p
  rcases p with ⟨j,i⟩
  simp [transpose_apply, mul_comm]

theorem summable_norm_row (R : MatrixL1 I J) : Summable (fun i => ‖row i R‖) := by
  have h := (summable_prod_of_nonneg (fun p : I × J => norm_nonneg (R p))).mp (summable_norm R)
  simp_rw [norm_eq_tsum, row_apply]
  exact h.2

theorem tsum_norm_row (R : MatrixL1 I J) : (∑' i, ‖row i R‖) = ‖R‖ := by
  simp only [norm_eq_tsum, row_apply]
  exact (summable_norm R).tsum_prod.symm

theorem summable_norm_applyRight (D : L1 J →L[ℝ] L1 J) (R : MatrixL1 I J) :
    Summable (fun p : I × J => ‖D (row p.1 R) p.2‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun i => summable_norm (D (row i R)), ?_⟩
  have h : Summable (fun i => ‖D (row i R)‖) :=
    ((summable_norm_row R).mul_left ‖D‖).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun i => D.le_opNorm (row i R))
  simpa only [norm_eq_tsum] using h

def applyRight (D : L1 J →L[ℝ] L1 J) (R : MatrixL1 I J) : MatrixL1 I J :=
  ⟨fun p => D (row p.1 R) p.2, memℓp_gen (by simpa using summable_norm_applyRight D R)⟩

@[simp] theorem applyRight_apply (D : L1 J →L[ℝ] L1 J) (R : MatrixL1 I J) (i : I) (j : J) :
    applyRight D R (i,j) = D (row i R) j := rfl

theorem norm_applyRight_le (D : L1 J →L[ℝ] L1 J) (R : MatrixL1 I J) :
    ‖applyRight D R‖ ≤ ‖D‖ * ‖R‖ := by
  rw [norm_eq_tsum]
  change (∑' p : I × J, ‖D (row p.1 R) p.2‖) ≤ _
  rw [(summable_norm_applyRight D R).tsum_prod]
  change (∑' i, ∑' j, ‖D (row i R) j‖) ≤ _
  simp only [← norm_eq_tsum]
  calc
    (∑' i, ‖D (row i R)‖) ≤ ∑' i, ‖D‖ * ‖row i R‖ := by
      apply Summable.tsum_le_tsum (fun i => D.le_opNorm (row i R))
      · exact ((summable_norm_row R).mul_left ‖D‖).of_nonneg_of_le
          (fun _ => norm_nonneg _) (fun i => D.le_opNorm (row i R))
      · exact (summable_norm_row R).mul_left ‖D‖
    _ = ‖D‖ * ‖R‖ := by rw [tsum_mul_left, tsum_norm_row]

def mapRight (D : L1 J →L[ℝ] L1 J) : MatrixL1 I J →L[ℝ] MatrixL1 I J :=
  ({ toFun := applyRight D
     map_add' := by
       intro R Q; ext p
       change D (row p.1 (R+Q)) p.2 = D (row p.1 R) p.2 + D (row p.1 Q) p.2
       rw [map_add, map_add]
       rfl
     map_smul' := by intro c R; ext p; simp [applyRight] } :
    MatrixL1 I J →ₗ[ℝ] MatrixL1 I J).mkContinuous ‖D‖ (norm_applyRight_le D)

@[simp] theorem mapRight_apply (D : L1 J →L[ℝ] L1 J) (R : MatrixL1 I J) (i : I) (j : J) :
    mapRight D R (i,j) = D (row i R) j := rfl

@[simp] theorem mapRight_outer (D : L1 J →L[ℝ] L1 J) (x : L1 I) (y : L1 J) :
    mapRight D (outer x y) = outer x (D y) := by
  ext p
  rcases p with ⟨i,j⟩
  simp [mapRight_apply, row_outer]

def mapLeft (D : L1 I →L[ℝ] L1 I) : MatrixL1 I J →L[ℝ] MatrixL1 I J :=
  (transpose (I := I) (J := J)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((mapRight (I := J) D).comp
      (transpose (I := I) (J := J)).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem mapLeft_apply (D : L1 I →L[ℝ] L1 I) (R : MatrixL1 I J) (i : I) (j : J) :
    mapLeft D R (i,j) = D (col j R) i := rfl

@[simp] theorem mapLeft_outer (D : L1 I →L[ℝ] L1 I) (x : L1 I) (y : L1 J) :
    mapLeft D (outer x y) = outer (D x) y := by
  ext p
  rcases p with ⟨i,j⟩
  simp [mapLeft_apply, col_outer, mul_comm]

end NoBorelUpperBoundFSigma.L1Coordinates

end
end
-- END COMPLETE MODULE NoBorelUpperBound.L1Coordinates

-- BEGIN COMPLETE MODULE ModNullProof.Coordinates
section
                                             
                                      

set_option autoImplicit false
noncomputable section

namespace ModNullUniversality.CompactTensor

abbrev S := List ℕ
abbrev Space := ℝ × NoBorelUpperBoundFSigma.L1Coordinates.MatrixL1 S S
abbrev Index := Unit ⊕ (S × S)
abbrev Ambient := Index → ℝ

instance : MeasurableSpace Space := borel Space
instance : BorelSpace Space := ⟨rfl⟩

def coordinates : Space →ₗ[ℝ] Ambient where
  toFun p := Sum.elim (fun _ => p.1) (fun ij => p.2 ij)
  map_add' p q := by funext i; cases i <;> rfl
  map_smul' a p := by funext i; cases i <;> rfl

@[simp] theorem coordinates_left (p : Space) (u : Unit) :
    coordinates p (.inl u) = p.1 := rfl

@[simp] theorem coordinates_right (p : Space) (ij : S × S) :
    coordinates p (.inr ij) = p.2 ij := rfl

theorem coordinates_injective : Function.Injective coordinates := by
  intro p q h
  apply Prod.ext
  · exact congrFun h (.inl ())
  · ext ij
    exact congrFun h (.inr ij)

theorem continuous_coordinates : Continuous coordinates := by
  apply continuous_pi
  intro i
  cases i with
  | inl u => exact continuous_fst
  | inr ij =>
    exact (lp.evalCLM ℝ (fun _ : S × S => ℝ) 1 ij).continuous.comp continuous_snd

end ModNullUniversality.CompactTensor

end
end
-- END COMPLETE MODULE ModNullProof.Coordinates

-- BEGIN COMPLETE MODULE ModNullProof.CompactEmbedding
section
                               
                                              
                                                
                                           
                                               

set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace

namespace ModNullUniversality.CompactTensor

abbrev AddTarget := Index → ℕ → AddCircle (1 : ℝ)
abbrev Target := Multiplicative AddTarget

instance : MeasurableSpace Target := borel Target
instance : BorelSpace Target := ⟨rfl⟩
instance : MetrizableSpace Target := inferInstanceAs (MetrizableSpace AddTarget)

/-- Dividing by every positive integer separates real numbers modulo integers. -/
theorem real_eq_zero_of_div_mod_zero (x : ℝ)
    (hx : ∀ n : ℕ, ((x / ((n : ℝ) + 1) : ℝ) : AddCircle (1 : ℝ)) = 0) : x = 0 := by
  obtain ⟨N,hN⟩ := exists_nat_gt |x|
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hsmall : |x / ((N : ℝ) + 1)| < 1 := by
    rw [abs_div,abs_of_pos hpos,div_lt_one hpos]
    linarith
  obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (hx N)
  have hk' : (k : ℝ) = x / ((N : ℝ) + 1) := by simpa using hk
  rw [← hk'] at hsmall
  have hlo : (-1 : ℤ) < k := by exact_mod_cast (abs_lt.mp hsmall).1
  have hhi : k < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hsmall).2
  have hk0 : k = 0 := by omega
  have hz : x / ((N : ℝ) + 1) = 0 := by rw [← hk',hk0]; simp
  exact (div_eq_zero_iff.mp hz).resolve_right (ne_of_gt hpos)

def embedding : Ambient →+ AddTarget where
  toFun u i n := ((u i / ((n : ℝ) + 1) : ℝ) : AddCircle (1 : ℝ))
  map_zero' := by ext i n; simp
  map_add' u v := by
    ext i n
    change (((u i + v i) / ((n : ℝ) + 1) : ℝ) : AddCircle (1 : ℝ)) = _
    rw [add_div,AddCircle.coe_add]
    rfl

theorem continuous_embedding : Continuous embedding := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro n
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp ((continuous_apply i).div_const _)

theorem embedding_injective : Function.Injective embedding := by
  intro u v huv
  funext i
  apply sub_eq_zero.mp
  apply real_eq_zero_of_div_mod_zero
  intro n
  have h := congrFun (congrFun huv i) n
  change ((u i / ((n : ℝ) + 1) : ℝ) : AddCircle (1 : ℝ)) =
    ((v i / ((n : ℝ) + 1) : ℝ) : AddCircle (1 : ℝ)) at h
  rw [sub_div,AddCircle.coe_sub]
  exact sub_eq_zero.mpr h

def sourceEmbedding : Space →+ AddTarget := embedding.comp coordinates.toAddMonoidHom

theorem continuous_sourceEmbedding : Continuous sourceEmbedding :=
  continuous_embedding.comp continuous_coordinates

theorem sourceEmbedding_injective : Function.Injective sourceEmbedding :=
  embedding_injective.comp coordinates_injective

def fullCompact : PositiveCompacts Target :=
  ⟨⟨univ,isCompact_univ⟩,by simp⟩

def haar : Measure Target := Measure.haarMeasure fullCompact

instance : IsProbabilityMeasure haar := ⟨by exact Measure.haarMeasure_self⟩
instance : Measure.IsHaarMeasure haar := inferInstanceAs (Measure.IsHaarMeasure (Measure.haarMeasure fullCompact))

def compactGroup : CompactMetrizableHaarGroup where
  Carrier := Target
  group := inferInstance
  topology := inferInstance
  compact := inferInstance
  metrizable := inferInstance
  topologicalGroup := inferInstance
  measurable := inferInstance
  borelSpace := inferInstance
  haar := haar
  probability := inferInstance
  haarMeasure := inferInstance

theorem compactGroup_abelian : IsAbelian compactGroup := by
  change ∀ x y : Target, x * y = y * x
  intro x y
  exact mul_comm x y

end ModNullUniversality.CompactTensor

end
end
-- END COMPLETE MODULE ModNullProof.CompactEmbedding

-- BEGIN COMPLETE MODULE ModNullProof.BorelComplexity
section
                                          
                                              

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace

namespace ModNullUniversality

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem isFSigma_compl_of_isGdelta {s : Set X} (hs : IsGδ s) : IsFSigma sᶜ := by
  obtain ⟨U,hU,hseq⟩ := hs.eq_iInter_nat
  refine ⟨fun n => (U n)ᶜ,fun n => (hU n).isClosed_compl,?_⟩
  rw [hseq,compl_iInter]

theorem isGdelta_compl_of_isFSigma {s : Set X} (hs : IsFSigma s) : IsGδ sᶜ := by
  obtain ⟨C,hC,rfl⟩ := hs
  rw [compl_iUnion]
  exact IsGδ.iInter_of_isOpen (fun n => (hC n).isOpen_compl)

theorem differenceFSigma_isDelta3 [PseudoMetrizableSpace X] {s : Set X}
    (hs : DifferenceFSigma s) : IsDelta3 s := by
  obtain ⟨A,B,hA,hB,rfl⟩ := hs
  obtain ⟨C,hC,hseqA⟩ := hA
  obtain ⟨D,hD,hseqB⟩ := hB
  have hAc : IsGδ Aᶜ := isGdelta_compl_of_isFSigma ⟨C,hC,hseqA⟩
  have hBc : IsGδ Bᶜ := isGdelta_compl_of_isFSigma ⟨D,hD,hseqB⟩
  constructor
  · refine ⟨fun n => C n ∩ Bᶜ,fun n => (hC n).isGδ.inter hBc,?_⟩
    rw [hseqA]
    ext x
    simp only [mem_diff,mem_iUnion,mem_inter_iff,mem_compl_iff]
    aesop
  · refine ⟨fun n => (D n ∪ Aᶜ)ᶜ,
      fun n => isFSigma_compl_of_isGdelta ((hD n).isGδ.union hAc),?_⟩
    rw [hseqB]
    ext x
    simp only [mem_diff,mem_iUnion,mem_iInter,mem_compl_iff,mem_union,not_or,not_not]
    exact ⟨fun h i => ⟨fun hi => h.2 ⟨i,hi⟩,h.1⟩,
      fun h => ⟨(h 0).2,fun ⟨i,hi⟩ => (h i).1 hi⟩⟩

theorem isKSigma_image {s : Set X} (hs : IsKSigma s) (f : X → Y)
    (hf : Continuous f) : IsKSigma (f '' s) := by
  obtain ⟨C,hC,rfl⟩ := hs
  exact ⟨fun n => f '' C n,fun n => (hC n).image hf,by rw [image_iUnion]⟩

theorem isFSigma_of_isKSigma [T2Space X] {s : Set X} (hs : IsKSigma s) : IsFSigma s := by
  obtain ⟨C,hC,hseq⟩ := hs
  exact ⟨C,fun n => (hC n).isClosed,hseq⟩

theorem isKSigma_of_isFSigma [CompactSpace X] {s : Set X} (hs : IsFSigma s) : IsKSigma s := by
  obtain ⟨C,hC,hseq⟩ := hs
  exact ⟨C,fun n => (hC n).isCompact,hseq⟩

theorem isKSigma_subtype_image_of_isFSigma {K : Set X} (hK : IsCompact K)
    {s : Set K} (hs : IsFSigma s) : IsKSigma (Subtype.val '' s : Set X) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact isKSigma_image (isKSigma_of_isFSigma hs) Subtype.val continuous_subtype_val

theorem isFSigma_iUnion_nat {s : ℕ → Set X} (hs : ∀ n, IsFSigma (s n)) :
    IsFSigma (⋃ n, s n) := by
  classical
  choose C hC hseq using hs
  refine ⟨fun k => C k.unpair.1 k.unpair.2,fun k => hC _ _,?_⟩
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨n,hn⟩
    rw [hseq n] at hn
    obtain ⟨m,hm⟩ := mem_iUnion.mp hn
    exact ⟨Nat.pair n m,by simpa using hm⟩
  · rintro ⟨k,hk⟩
    refine ⟨k.unpair.1,?_⟩
    rw [hseq]
    exact mem_iUnion.mpr ⟨k.unpair.2,hk⟩

theorem isFSigma_iUnion {ι : Type*} [Countable ι] {s : ι → Set X}
    (hs : ∀ i, IsFSigma (s i)) : IsFSigma (⋃ i, s i) := by
  classical
  by_cases h : Nonempty ι
  · letI := h
    obtain ⟨e,he⟩ := exists_surjective_nat ι
    have hseq : (⋃ i, s i) = ⋃ n : ℕ, s (e n) := by
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨i,hi⟩
        obtain ⟨n,rfl⟩ := he i
        exact ⟨n,hi⟩
      · rintro ⟨n,hn⟩
        exact ⟨e n,hn⟩
    rw [hseq]
    exact isFSigma_iUnion_nat (fun n => hs (e n))
  · letI : IsEmpty ι := ⟨fun i => h ⟨i⟩⟩
    exact ⟨fun _ => ∅,fun _ => isClosed_empty,by ext x; simp⟩

theorem isFSigma_inter {s t : Set X} (hs : IsFSigma s) (ht : IsFSigma t) :
    IsFSigma (s ∩ t) := by
  obtain ⟨C,hC,rfl⟩ := hs
  obtain ⟨D,hD,rfl⟩ := ht
  refine ⟨fun k => C k.unpair.1 ∩ D k.unpair.2,
    fun k => (hC _).inter (hD _),?_⟩
  ext x
  simp only [mem_inter_iff,mem_iUnion]
  constructor
  · rintro ⟨⟨i,hi⟩,⟨j,hj⟩⟩
    exact ⟨Nat.pair i j,by simpa using And.intro hi hj⟩
  · rintro ⟨k,hk⟩
    exact ⟨⟨k.unpair.1,hk.1⟩,⟨k.unpair.2,hk.2⟩⟩

theorem differenceFSigma_image_of_ksigma [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hinj : Function.Injective f)
    (A B : Set X) (hA : IsKSigma A) (hB : IsKSigma B) :
    DifferenceFSigma (f '' (A \ B)) := by
  refine ⟨f '' A,f '' B,isFSigma_of_isKSigma (isKSigma_image hA f hf),
    isFSigma_of_isKSigma (isKSigma_image hB f hf),?_⟩
  ext y
  constructor
  · rintro ⟨x,⟨hxA,hxB⟩,rfl⟩
    refine ⟨mem_image_of_mem f hxA,?_⟩
    rintro ⟨z,hz,hzx⟩
    exact hxB ((hinj hzx) ▸ hz)
  · rintro ⟨⟨x,hx,hxy⟩,hnot⟩
    refine ⟨x,⟨hx,?_⟩,hxy⟩
    intro hxB
    exact hnot ⟨x,hxB,hxy⟩

theorem isFSigma_preimage {s : Set Y} (hs : IsFSigma s) (f : X → Y)
    (hf : Continuous f) : IsFSigma (f ⁻¹' s) := by
  obtain ⟨C,hC,rfl⟩ := hs
  exact ⟨fun n => f ⁻¹' C n,fun n => (hC n).preimage hf,by rw [preimage_iUnion]⟩

theorem differenceFSigma_preimage {s : Set Y} (hs : DifferenceFSigma s) (f : X → Y)
    (hf : Continuous f) : DifferenceFSigma (f ⁻¹' s) := by
  obtain ⟨A,B,hA,hB,rfl⟩ := hs
  exact ⟨f ⁻¹' A,f ⁻¹' B,isFSigma_preimage hA f hf,isFSigma_preimage hB f hf,rfl⟩

theorem isFSigma_measurableSet [MeasurableSpace X] [BorelSpace X]
    {s : Set X} (hs : IsFSigma s) : MeasurableSet s := by
  obtain ⟨C,hC,rfl⟩ := hs
  exact MeasurableSet.iUnion (fun n => (hC n).measurableSet)

theorem differenceFSigma_measurableSet [MeasurableSpace X] [BorelSpace X]
    {s : Set X} (hs : DifferenceFSigma s) : MeasurableSet s := by
  obtain ⟨A,B,hA,hB,rfl⟩ := hs
  exact (isFSigma_measurableSet hA).diff (isFSigma_measurableSet hB)

end ModNullUniversality

end
end
-- END COMPLETE MODULE ModNullProof.BorelComplexity

-- BEGIN COMPLETE MODULE NoBorelUpperBound.NilpotentGroup
section
                                                        
                                                
                                           
                     

noncomputable section
open Set Topology

namespace NoBorelUpperBoundFSigma

universe u v
variable {X : Type u} {C : Type v}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- A central extension associated with a real continuous bilinear map. -/
def CentralExtension (β : X →L[ℝ] X →L[ℝ] C) := X × X × C

namespace CentralExtension
variable (β : X →L[ℝ] X →L[ℝ] C)

instance : TopologicalSpace (CentralExtension β) :=
  inferInstanceAs (TopologicalSpace (X × X × C))

instance [PolishSpace X] [PolishSpace C] : PolishSpace (CentralExtension β) :=
  inferInstanceAs (PolishSpace (X × X × C))

instance : Group (CentralExtension β) where
  mul a b := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2 + β a.1 b.2.1)
  one := (0, 0, 0)
  inv a := (-a.1, -a.2.1, -a.2.2 + β a.1 a.2.1)
  mul_assoc a b c := by
    apply Prod.ext
    · exact add_assoc _ _ _
    · apply Prod.ext
      · exact add_assoc _ _ _
      · change (a.2.2 + b.2.2 + β a.1 b.2.1) + c.2.2 + β (a.1 + b.1) c.2.1 =
          a.2.2 + (b.2.2 + c.2.2 + β b.1 c.2.1) + β a.1 (b.2.1 + c.2.1)
        simp only [map_add, ContinuousLinearMap.add_apply]
        abel
  one_mul a := by
    apply Prod.ext
    · exact zero_add _
    · apply Prod.ext
      · exact zero_add _
      · change (0 : C) + a.2.2 + β 0 a.2.1 = a.2.2
        simp
  mul_one a := by
    apply Prod.ext
    · exact add_zero _
    · apply Prod.ext
      · exact add_zero _
      · change a.2.2 + (0 : C) + β a.1 0 = a.2.2
        simp
  inv_mul_cancel a := by
    apply Prod.ext
    · exact neg_add_cancel _
    · apply Prod.ext
      · exact neg_add_cancel _
      · change (-a.2.2 + β a.1 a.2.1) + a.2.2 + β (-a.1) a.2.1 = 0
        simp only [map_neg, ContinuousLinearMap.neg_apply]
        abel

@[simp] theorem one_def : (1 : CentralExtension β) = (0, 0, 0) := rfl
theorem mul_def (a b : CentralExtension β) :
    a * b = (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2 + β a.1 b.2.1) := rfl
theorem inv_def (a : CentralExtension β) :
    a⁻¹ = (-a.1, -a.2.1, -a.2.2 + β a.1 a.2.1) := rfl

instance : IsTopologicalGroup (CentralExtension β) where
  continuous_mul := by
    change Continuous (fun p : (X × X × C) × (X × X × C) =>
      (p.1.1 + p.2.1, p.1.2.1 + p.2.2.1, p.1.2.2 + p.2.2.2 + β p.1.1 p.2.2.1))
    exact (continuous_fst.fst.add continuous_snd.fst).prodMk
      ((continuous_fst.snd.fst.add continuous_snd.snd.fst).prodMk
        ((continuous_fst.snd.snd.add continuous_snd.snd.snd).add
          (β.continuous₂.comp (continuous_fst.fst.prodMk continuous_snd.snd.fst))))
  continuous_inv := by
    change Continuous (fun a : X × X × C => (-a.1, -a.2.1, -a.2.2 + β a.1 a.2.1))
    exact continuous_fst.neg.prodMk
      (continuous_snd.fst.neg.prodMk (continuous_snd.snd.neg.add
        (β.continuous₂.comp (continuous_fst.prodMk continuous_snd.fst))))

def left (x : X) : CentralExtension β := (x, 0, 0)
def right (y : X) : CentralExtension β := (0, y, 0)
def center (c : C) : CentralExtension β := (0, 0, c)

@[simp] theorem left_mul (x x' : X) : left β x * left β x' = left β (x + x') := by
  simp [left, mul_def]
@[simp] theorem right_mul (y y' : X) : right β y * right β y' = right β (y + y') := by
  simp [right, mul_def]
@[simp] theorem center_mul (c c' : C) : center β c * center β c' = center β (c + c') := by
  simp [center, mul_def]
@[simp] theorem center_inv (c : C) : (center β c)⁻¹ = center β (-c) := by
  simp [center, inv_def]

def leftHom : Multiplicative X →* CentralExtension β where
  toFun x := left β x.toAdd
  map_one' := rfl
  map_mul' x y := (left_mul β x.toAdd y.toAdd).symm

def rightHom : Multiplicative X →* CentralExtension β where
  toFun y := right β y.toAdd
  map_one' := rfl
  map_mul' x y := (right_mul β x.toAdd y.toAdd).symm

def centerHom : Multiplicative C →* CentralExtension β where
  toFun c := center β c.toAdd
  map_one' := rfl
  map_mul' c d := (center_mul β c.toAdd d.toAdd).symm

theorem mixed_commutator (x y : X) :
    left β x * right β y * (left β x)⁻¹ * (right β y)⁻¹ = center β (β x y) := by
  simp [left, right, center, mul_def, inv_def]

theorem coordinate_factorization (a : CentralExtension β) :
    a = left β a.1 * right β a.2.1 * center β (a.2.2 - β a.1 a.2.1) := by
  simp [left, right, center, mul_def]

theorem center_commutes (c : C) (a : CentralExtension β) :
    center β c * a = a * center β c := by
  simp [center, mul_def, add_comm]

end CentralExtension
end NoBorelUpperBoundFSigma

end
end
-- END COMPLETE MODULE NoBorelUpperBound.NilpotentGroup

-- BEGIN COMPLETE MODULE NoBorelUpperBound.NilpotentGenerated
section
                                       

noncomputable section
open Set Topology

namespace NoBorelUpperBoundFSigma.CentralExtension
universe u v w
variable {A : Type u} {X : Type v} {C : Type w}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
variable (β : X →L[ℝ] X →L[ℝ] C)

def coordinateSubgroup (H : Submodule ℝ X) (K : Submodule ℝ C)
    (hβ : ∀ x ∈ H, ∀ y ∈ H, β x y ∈ K) : Subgroup (CentralExtension β) where
  carrier := {g | g.1 ∈ H ∧ g.2.1 ∈ H ∧ g.2.2 ∈ K}
  one_mem' := ⟨H.zero_mem,H.zero_mem,K.zero_mem⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨H.add_mem ha.1 hb.1,H.add_mem ha.2.1 hb.2.1,
      K.add_mem (K.add_mem ha.2.2 hb.2.2) (hβ a.1 ha.1 b.2.1 hb.2.1)⟩
  inv_mem' := by
    intro a ha
    exact ⟨H.neg_mem ha.1,H.neg_mem ha.2.1,
      K.add_mem (K.neg_mem ha.2.2) (hβ a.1 ha.1 a.2.1 ha.2.1)⟩

@[simp] theorem mem_coordinateSubgroup (H : Submodule ℝ X) (K : Submodule ℝ C)
    (hβ : ∀ x ∈ H, ∀ y ∈ H, β x y ∈ K) (g : CentralExtension β) :
    g ∈ coordinateSubgroup β H K hβ ↔ g.1 ∈ H ∧ g.2.1 ∈ H ∧ g.2.2 ∈ K := Iff.rfl

def centralSpan (j : A →L[ℝ] X) : Submodule ℝ C :=
  Submodule.span ℝ (range (fun p : A×A => β (j p.1) (j p.2)))

theorem beta_mem_centralSpan (j : A →L[ℝ] X) (a b : A) :
    β (j a) (j b) ∈ centralSpan β j := Submodule.subset_span (mem_range_self (a,b))

theorem beta_range_mem_centralSpan (j : A →L[ℝ] X) :
    ∀ x ∈ j.range, ∀ y ∈ j.range, β x y ∈ centralSpan β j := by
  rintro x ⟨a,rfl⟩ y ⟨b,rfl⟩
  exact beta_mem_centralSpan β j a b

def generatedAxes (j : A →L[ℝ] X) : Subgroup (CentralExtension β) :=
  Subgroup.closure (range (fun a => left β (j a)) ∪ range (fun a => right β (j a)))

theorem left_mem_generatedAxes (j : A →L[ℝ] X) (a : A) :
    left β (j a) ∈ generatedAxes β j :=
  Subgroup.subset_closure (Or.inl (mem_range_self a))

theorem right_mem_generatedAxes (j : A →L[ℝ] X) (a : A) :
    right β (j a) ∈ generatedAxes β j :=
  Subgroup.subset_closure (Or.inr (mem_range_self a))

theorem center_generator_mem_generatedAxes (j : A →L[ℝ] X) (a b : A) :
    center β (β (j a) (j b)) ∈ generatedAxes β j := by
  rw [← mixed_commutator]
  exact (generatedAxes β j).mul_mem
    ((generatedAxes β j).mul_mem
      ((generatedAxes β j).mul_mem (left_mem_generatedAxes β j a) (right_mem_generatedAxes β j b))
      ((generatedAxes β j).inv_mem (left_mem_generatedAxes β j a)))
    ((generatedAxes β j).inv_mem (right_mem_generatedAxes β j b))

theorem center_mem_generatedAxes (j : A →L[ℝ] X) {c : C} (hc : c ∈ centralSpan β j) :
    center β c ∈ generatedAxes β j := by
  have hstrong : ∀ c ∈ centralSpan β j, ∀ r : ℝ, center β (r • c) ∈ generatedAxes β j := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨⟨a,b⟩,rfl⟩ := hc
      intro r
      have heq : r • β (j a) (j b) = β (j (r • a)) (j b) := by simp
      rw [heq]
      exact center_generator_mem_generatedAxes β j (r • a) b
    | zero =>
      intro r
      simpa [center] using (generatedAxes β j).one_mem
    | add c d hc hd IHc IHd =>
      intro r
      rw [smul_add,← center_mul]
      exact (generatedAxes β j).mul_mem (IHc r) (IHd r)
    | smul a c hc IH =>
      intro r
      rw [smul_smul]
      exact IH (r*a)
  simpa only [one_smul] using hstrong c hc 1

theorem generatedAxes_eq_coordinateSubgroup (j : A →L[ℝ] X) :
    generatedAxes β j = coordinateSubgroup β j.range (centralSpan β j) (beta_range_mem_centralSpan β j) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with ⟨a,rfl⟩ | ⟨a,rfl⟩
    · exact ⟨⟨a,rfl⟩,j.range.zero_mem,(centralSpan β j).zero_mem⟩
    · exact ⟨j.range.zero_mem,⟨a,rfl⟩,(centralSpan β j).zero_mem⟩
  · intro g hg
    rcases hg with ⟨⟨a,ha⟩,⟨b,hb⟩,hc⟩
    rw [coordinate_factorization β g]
    apply (generatedAxes β j).mul_mem
    · apply (generatedAxes β j).mul_mem
      · rw [← ha]
        exact left_mem_generatedAxes β j a
      · rw [← hb]
        exact right_mem_generatedAxes β j b
    · apply center_mem_generatedAxes β j
      apply (centralSpan β j).sub_mem hc
      rw [← ha,← hb]
      exact beta_mem_centralSpan β j a b

theorem isFSigma_coordinateSubgroup (H : Submodule ℝ X) (K : Submodule ℝ C)
    (hβ : ∀ x ∈ H, ∀ y ∈ H, β x y ∈ K)
    (hH : IsClosed (H : Set X)) (hK : NoUniversalFSigma.IsFSigma (K : Set C)) :
    NoUniversalFSigma.IsFSigma (coordinateSubgroup β H K hβ : Set (CentralExtension β)) := by
  obtain ⟨S,hS,hcover⟩ := hK
  refine ⟨fun n => {g | g.1 ∈ H ∧ g.2.1 ∈ H ∧ g.2.2 ∈ S n},?_,?_⟩
  · intro n
    exact (hH.preimage continuous_fst).inter
      ((hH.preimage continuous_snd.fst).inter ((hS n).preimage continuous_snd.snd))
  · ext g
    change (g.1 ∈ H ∧ g.2.1 ∈ H ∧ g.2.2 ∈ K) ↔ _
    change (g.1 ∈ H ∧ g.2.1 ∈ H ∧ g.2.2 ∈ (K : Set C)) ↔ _
    rw [hcover]
    simp only [mem_iUnion,mem_setOf_eq]
    aesop

theorem isFSigma_generatedAxes (j : A →L[ℝ] X)
    (hj : IsClosed (j.range : Set X))
    (hC : NoUniversalFSigma.IsFSigma (centralSpan β j : Set C)) :
    NoUniversalFSigma.IsFSigma (generatedAxes β j : Set (CentralExtension β)) := by
  rw [generatedAxes_eq_coordinateSubgroup]
  exact isFSigma_coordinateSubgroup β _ _ _ hj hC

end NoBorelUpperBoundFSigma.CentralExtension

end
end
-- END COMPLETE MODULE NoBorelUpperBound.NilpotentGenerated

-- BEGIN COMPLETE MODULE NoBorelUpperBound.SymmetricTensorLinear
section
                                      
                                        
                                        
                                            
                                                      
                                        
                     

noncomputable section

open Set Matrix
open scoped BigOperators

namespace NoBorelUpperBoundFSigma
namespace TensorAlgebra

/-- Finitely many independent coordinate vectors admit a nonsingular coordinate
minor. The coordinate index type itself can be infinite. -/
theorem exists_coordinate_pivot {I : Type*} {r : ℕ} (f : Fin r → I → ℝ)
    (hf : LinearIndependent ℝ f) :
    ∃ rows : Fin r → I, Matrix.det (fun i j => f j (rows i)) ≠ 0 := by
  have htop : Submodule.span ℝ (range (Function.swap f)) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hf
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ (Function.swap f)
  let b : Module.Basis κ ℝ (Fin r → ℝ) := Module.Basis.mk hli (by rw [hspan, htop])
  letI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card κ = r := by
    rw [← Module.finrank_eq_card_basis b]
    simp
  let e : Fin r ≃ κ := Fintype.equivOfCardEq (by simpa using hcard.symm)
  refine ⟨a ∘ e, ?_⟩
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  exact hli.comp e e.injective

end TensorAlgebra
end NoBorelUpperBoundFSigma


namespace NoBorelUpperBoundFSigma.TensorAlgebra

/-- The algebraic column space of an infinite real matrix. -/
def columnSpace {I J : Type*} (A : I → J → ℝ) : Submodule ℝ (I → ℝ) :=
  Submodule.span ℝ (range (fun j i => A i j))

/-- Finite-dimensional column spaces have a basis consisting of actual columns. -/
theorem exists_column_basis {I J : Type*} (A : I → J → ℝ)
    [FiniteDimensional ℝ (columnSpace A)] :
    ∃ r : ℕ, ∃ cols : Fin r → J,
      LinearIndependent ℝ (fun t i => A i (cols t)) ∧
      Submodule.span ℝ (range (fun t i => A i (cols t))) = columnSpace A := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ (fun j i => A i j)
  have hspan' : Submodule.span ℝ (range ((fun j i => A i j) ∘ a)) = columnSpace A := hspan
  letI : FiniteDimensional ℝ (Submodule.span ℝ (range ((fun j i => A i j) ∘ a))) :=
    hspan'.symm ▸ inferInstance
  letI : Fintype κ := FiniteDimensional.fintypeBasisIndex (Module.Basis.span hli)
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ, a ∘ e, hli.comp e e.injective, ?_⟩
  have hrange : range (fun t i => A i ((a ∘ e) t)) =
      range ((fun j i => A i j) ∘ a) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨e t, rfl⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨t, rfl⟩ := e.surjective k
      exact ⟨t, rfl⟩
  rw [hrange]
  exact hspan'

/-- A nonsingular pivot reconstructs every column once the selected columns span
all the columns. The adjugate form makes reconstruction polynomial. -/
theorem pivot_reconstruction {I J : Type*} {r : ℕ}
    (A : I → J → ℝ) (cols : Fin r → J) (rows : Fin r → I)
    (hspan : ∀ j, (fun i => A i j) ∈
      Submodule.span ℝ (range (fun t i => A i (cols t)))) (i : I) (j : J) :
    Matrix.det (fun s t => A (rows s) (cols t)) * A i j =
      (fun t => A i (cols t)) ⬝ᵥ
        ((Matrix.adjugate (fun s t => A (rows s) (cols t))) *ᵥ (fun s => A (rows s) j)) := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hspan j)
  have heq (a : I) : ∑ t, c t * A a (cols t) = A a j := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hc a
  have hvec : (fun s => A (rows s) j) =
      (fun s t => A (rows s) (cols t)) *ᵥ c := by
    funext s
    simpa only [Matrix.mulVec, dotProduct, mul_comm] using (heq (rows s)).symm
  rw [hvec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul]
  congr 1
  simpa only [dotProduct, mul_comm] using (heq i).symm

/-- Every finite-rank coordinate matrix has a nonsingular finite pivot and an
exact polynomial row-column reconstruction. -/
theorem exists_finite_pivot {I J : Type*} (A : I → J → ℝ)
    [FiniteDimensional ℝ (columnSpace A)] :
    ∃ r : ℕ, ∃ cols : Fin r → J, ∃ rows : Fin r → I,
      Matrix.det (fun s t => A (rows s) (cols t)) ≠ 0 ∧
      ∀ i j, Matrix.det (fun s t => A (rows s) (cols t)) * A i j =
        (fun t => A i (cols t)) ⬝ᵥ
          (Matrix.adjugate (fun s t => A (rows s) (cols t)) *ᵥ (fun s => A (rows s) j)) := by
  obtain ⟨r, cols, hli, hspan⟩ := exists_column_basis A
  obtain ⟨rows, hdet⟩ := exists_coordinate_pivot (fun t i => A i (cols t)) hli
  refine ⟨r, cols, rows, hdet, pivot_reconstruction A cols rows ?_⟩
  intro j
  rw [hspan]
  exact Submodule.subset_span (mem_range_self j)

end NoBorelUpperBoundFSigma.TensorAlgebra


namespace NoBorelUpperBoundFSigma.TensorAlgebra

@[simp] theorem columnSpace_zero {I J : Type*} :
    columnSpace (fun (_ : I) (_ : J) => (0 : ℝ)) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact Submodule.zero_mem _

theorem columnSpace_add_le {I J : Type*} (A B : I → J → ℝ) :
    columnSpace (fun i j => A i j + B i j) ≤ columnSpace A ⊔ columnSpace B := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact (columnSpace A ⊔ columnSpace B).add_mem
    (Submodule.mem_sup_left (Submodule.subset_span (mem_range_self j)))
    (Submodule.mem_sup_right (Submodule.subset_span (mem_range_self j)))

theorem columnSpace_smul_le {I J : Type*} (c : ℝ) (A : I → J → ℝ) :
    columnSpace (fun i j => c * A i j) ≤ columnSpace A := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact (columnSpace A).smul_mem c (Submodule.subset_span (mem_range_self j))

end NoBorelUpperBoundFSigma.TensorAlgebra







end
end
-- END COMPLETE MODULE NoBorelUpperBound.SymmetricTensorLinear

-- BEGIN COMPLETE MODULE NoBorelUpperBound.SymmetricTensor
section
                                              

noncomputable section
open Set Matrix
open scoped BigOperators

namespace NoBorelUpperBoundFSigma.SymmetricTensor
open L1Coordinates TensorAlgebra
universe u
variable {I : Type u}

def algebraicSpan : Submodule ℝ (MatrixL1 I I) :=
  Submodule.span ℝ (range (fun p : L1 I × L1 I => outer p.1 p.2))

def sym (a b : L1 I) : MatrixL1 I I := (1 / 2 : ℝ) • (outer a b + outer b a)

def symmetricSpan : Submodule ℝ (MatrixL1 I I) :=
  Submodule.span ℝ (range (fun p : L1 I × L1 I => sym p.1 p.2))

theorem sym_mem (a b : L1 I) : sym a b ∈ symmetricSpan :=
  Submodule.subset_span (mem_range_self (a,b))

theorem outer_mem (a b : L1 I) : outer a b ∈ algebraicSpan :=
  Submodule.subset_span (mem_range_self (a,b))

theorem symmetricSpan_le_algebraicSpan : symmetricSpan (I := I) ≤ algebraicSpan := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a,b⟩,rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (outer_mem a b) (outer_mem b a))

theorem transpose_eq_of_mem_symmetricSpan {K : MatrixL1 I I} (hK : K ∈ symmetricSpan) :
    transpose K = K := by
  induction hK using Submodule.span_induction with
  | mem K hK =>
    obtain ⟨⟨a,b⟩,rfl⟩ := hK
    simp only [sym,map_smul,map_add,transpose_outer,add_comm]
  | zero => exact map_zero _
  | add x y hx hy IHx IHy => simp only [map_add,IHx,IHy]
  | smul a x hx IH => simp only [map_smul,IH]

theorem symmetric_of_mem {K : MatrixL1 I I} (hK : K ∈ symmetricSpan) (i j : I) :
    K (i,j) = K (j,i) := by
  have h := congrArg (fun Q : MatrixL1 I I => Q (j,i)) (transpose_eq_of_mem_symmetricSpan hK)
  exact h

def symmetrize : MatrixL1 I I →L[ℝ] MatrixL1 I I :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ _ + transpose.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem symmetrize_outer (a b : L1 I) : symmetrize (outer a b) = sym a b := by
  change (1 / 2 : ℝ) • (outer a b + transpose (outer a b)) = _
  rw [transpose_outer]
  rfl

theorem symmetrize_mem {K : MatrixL1 I I} (hK : K ∈ algebraicSpan) :
    symmetrize K ∈ symmetricSpan := by
  induction hK using Submodule.span_induction with
  | mem K hK => obtain ⟨⟨a,b⟩,rfl⟩ := hK; simpa using sym_mem a b
  | zero => simpa using (symmetricSpan (I := I)).zero_mem
  | add x y hx hy IHx IHy => simpa only [map_add] using Submodule.add_mem _ IHx IHy
  | smul a x hx IH => simpa only [map_smul] using Submodule.smul_mem _ a IH

theorem mem_symmetricSpan_iff {K : MatrixL1 I I} :
    K ∈ symmetricSpan ↔ K ∈ algebraicSpan ∧ transpose K = K := by
  refine ⟨fun h => ⟨symmetricSpan_le_algebraicSpan h,transpose_eq_of_mem_symmetricSpan h⟩, ?_⟩
  rintro ⟨hK,hT⟩
  have h := symmetrize_mem hK
  have heq : symmetrize K = K := by
    change (1/2 : ℝ) • (K + transpose K) = K
    rw [hT]
    module
  rwa [heq] at h

def imageMap (D : L1 I →L[ℝ] L1 I) (o : I) : MatrixL1 I I →L[ℝ] ℝ × MatrixL1 I I :=
  (lp.evalCLM ℝ (fun _ : I×I => ℝ) 1 (o,o)).prod (mapLeft D)

def imageSubmodule (D : L1 I →L[ℝ] L1 I) (o : I) : Submodule ℝ (ℝ × MatrixL1 I I) :=
  symmetricSpan.map (imageMap D o).toLinearMap

@[simp] theorem imageMap_apply (D : L1 I →L[ℝ] L1 I) (o : I) (K : MatrixL1 I I) :
    imageMap D o K = (K (o,o),mapLeft D K) := rfl

theorem mem_imageSubmodule (D : L1 I →L[ℝ] L1 I) (o : I) (K : MatrixL1 I I)
    (hK : K ∈ symmetricSpan) : (K (o,o),mapLeft D K) ∈ imageSubmodule D o :=
  ⟨K,hK,rfl⟩

@[simp] theorem mapLeft_sym (D : L1 I →L[ℝ] L1 I) (a b : L1 I) :
    mapLeft D (sym a b) = (1/2 : ℝ) • (outer (D a) b + outer (D b) a) := by
  simp only [sym,map_smul,map_add,mapLeft_outer]

def symBilinear : L1 I →L[ℝ] L1 I →L[ℝ] MatrixL1 I I :=
  (1/2 : ℝ) • ((outerBilinear (I := I) (J := I)) + outerBilinear.flip)

@[simp] theorem symBilinear_apply (a b : L1 I) : symBilinear a b = sym a b := rfl

end NoBorelUpperBoundFSigma.SymmetricTensor

end
end
-- END COMPLETE MODULE NoBorelUpperBound.SymmetricTensor

-- BEGIN COMPLETE MODULE NoBorelUpperBound.SymmetricTensorCharts
section
                                        

noncomputable section
open Set Matrix
open scoped BigOperators

namespace NoBorelUpperBoundFSigma.SymmetricTensor
open L1Coordinates TensorAlgebra
universe u
variable {I : Type u}

def pivotD (D : L1 I →L[ℝ] L1 I) {r : ℕ} (rows qs : Fin r → I)
    (R : MatrixL1 I I) : Matrix (Fin r) (Fin r) ℝ :=
  fun j i => D (row (rows i) R) (qs j)

def liftNumerator (D : L1 I →L[ℝ] L1 I) {r : ℕ} (rows qs : Fin r → I)
    (R : MatrixL1 I I) : MatrixL1 I I :=
  ∑ i, ∑ j, (pivotD D rows qs R).adjugate i j • outer (row (rows i) R) (row (qs j) R)

theorem liftNumerator_mem_algebraicSpan (D : L1 I →L[ℝ] L1 I) {r : ℕ}
    (rows qs : Fin r → I) (R : MatrixL1 I I) : liftNumerator D rows qs R ∈ algebraicSpan := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (outer_mem _ _)

theorem continuous_pivotD (D : L1 I →L[ℝ] L1 I) {r : ℕ} (rows qs : Fin r → I) :
    Continuous (pivotD D rows qs) :=
  continuous_pi fun j => continuous_pi fun i =>
    (lp.evalCLM ℝ (fun _ : I => ℝ) 1 (qs j)).continuous.comp
      (D.continuous.comp (row (rows i)).continuous)

theorem continuous_liftNumerator (D : L1 I →L[ℝ] L1 I) {r : ℕ} (rows qs : Fin r → I) :
    Continuous (liftNumerator D rows qs) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  apply Continuous.smul
  · exact (continuous_apply j).comp ((continuous_apply i).comp
      (continuous_pivotD D rows qs).matrix_adjugate)
  · exact continuous_outer.comp ((row (rows i)).continuous.prodMk (row (qs j)).continuous)

/-- Closed reconstruction charts. Both matrix reconstruction and symmetry
are polynomial identities, so no closed-range assumption on D is used. -/
def imageChart (D : L1 I →L[ℝ] L1 I) (o : I) {r : ℕ} (rows qs : Fin r → I) (m : ℕ) :
    Set (ℝ × MatrixL1 I I) :=
  {p | (1 : ℝ)/(m+1) ≤ |(pivotD D rows qs p.2).det| ∧
    (pivotD D rows qs p.2).det • p.2 = mapLeft D (liftNumerator D rows qs p.2) ∧
    transpose (liftNumerator D rows qs p.2) = liftNumerator D rows qs p.2 ∧
    (pivotD D rows qs p.2).det * p.1 = liftNumerator D rows qs p.2 (o,o)}

theorem isClosed_imageChart (D : L1 I →L[ℝ] L1 I) (o : I) {r : ℕ}
    (rows qs : Fin r → I) (m : ℕ) : IsClosed (imageChart D o rows qs m) := by
  have hp : Continuous (fun p : ℝ × MatrixL1 I I => (pivotD D rows qs p.2).det) :=
    (continuous_pivotD D rows qs).matrix_det.comp continuous_snd
  have hl : Continuous (fun p : ℝ × MatrixL1 I I => liftNumerator D rows qs p.2) :=
    (continuous_liftNumerator D rows qs).comp continuous_snd
  apply IsClosed.inter (isClosed_le continuous_const hp.abs)
  apply IsClosed.inter (isClosed_eq (hp.smul continuous_snd) ((mapLeft D).continuous.comp hl))
  apply IsClosed.inter (isClosed_eq (transpose.continuous.comp hl) hl)
  exact isClosed_eq (hp.mul continuous_fst)
    ((lp.evalCLM ℝ (fun _ : I×I => ℝ) 1 (o,o)).continuous.comp hl)

theorem imageChart_subset_image (D : L1 I →L[ℝ] L1 I) (o : I) {r : ℕ}
    (rows qs : Fin r → I) (m : ℕ) : imageChart D o rows qs m ⊆ imageSubmodule D o := by
  rintro ⟨lam,R⟩ ⟨hd,hrec,hsym,hscalar⟩
  let d := (pivotD D rows qs R).det
  have hd0 : d ≠ 0 := abs_pos.mp ((by positivity : (0:ℝ)<1/(m+1)).trans_le hd)
  let K := d⁻¹ • liftNumerator D rows qs R
  have hK : K ∈ symmetricSpan := by
    apply mem_symmetricSpan_iff.mpr
    refine ⟨Submodule.smul_mem _ _ (liftNumerator_mem_algebraicSpan D rows qs R), ?_⟩
    change transpose (d⁻¹ • liftNumerator D rows qs R) = _
    rw [map_smul,hsym]
  refine ⟨K,hK,Prod.ext ?_ ?_⟩
  · change d⁻¹ * liftNumerator D rows qs R (o,o) = lam
    change d * lam = liftNumerator D rows qs R (o,o) at hscalar
    rw [← hscalar,← mul_assoc,inv_mul_cancel₀ hd0,one_mul]
  · change mapLeft D (d⁻¹ • liftNumerator D rows qs R) = R
    rw [map_smul,← hrec,smul_smul,inv_mul_cancel₀ hd0,one_smul]

abbrev ChartIndex (I : Type u) := Σ r : ℕ, (Fin r → I) × (Fin r → I) × ℕ

/-- Explicit infrastructure statement: the algebraic coverage argument is
the remaining premise; closedness of every actual chart is already proved. -/
theorem isFSigma_image_of_chart_coverage [Countable I]
    (D : L1 I →L[ℝ] L1 I) (o : I)
    (hcoverage : ∀ p ∈ imageSubmodule D o, ∃ r : ℕ, ∃ rows qs : Fin r → I,
      ∃ m : ℕ, p ∈ imageChart D o rows qs m) :
    NoUniversalFSigma.IsFSigma (imageSubmodule D o : Set (ℝ × MatrixL1 I I)) := by
  classical
  obtain ⟨e,he⟩ := exists_surjective_nat (Option (ChartIndex I))
  let C : Option (ChartIndex I) → Set (ℝ × MatrixL1 I I) := fun k =>
    match k with
    | none => ∅
    | some ⟨_,rows,qs,m⟩ => imageChart D o rows qs m
  refine ⟨fun n => C (e n), ?_, ?_⟩
  · intro n
    rcases h : e n with _ | ⟨r,rows,qs,m⟩
    · simpa only [h,C] using (isClosed_empty : IsClosed (∅ : Set (ℝ × MatrixL1 I I)))
    · simpa only [h,C] using isClosed_imageChart D o rows qs m
  · ext p
    constructor
    · intro hp
      obtain ⟨r,rows,qs,m,hm⟩ := hcoverage p hp
      obtain ⟨n,hn⟩ := he (some ⟨r,rows,qs,m⟩)
      exact mem_iUnion.mpr ⟨n,by simpa only [hn,C] using hm⟩
    · intro hp
      obtain ⟨n,hn⟩ := mem_iUnion.mp hp
      rcases h : e n with _ | ⟨r,rows,qs,m⟩
      · simpa only [h,C,mem_empty_iff_false] using hn
      · exact imageChart_subset_image D o rows qs m (by simpa only [h,C] using hn)

end NoBorelUpperBoundFSigma.SymmetricTensor

end
end
-- END COMPLETE MODULE NoBorelUpperBound.SymmetricTensorCharts

-- BEGIN COMPLETE MODULE NoBorelUpperBound.SymmetricTensorRank
section
                                        

noncomputable section
open Set Matrix
open scoped BigOperators

namespace NoBorelUpperBoundFSigma.SymmetricTensor
open L1Coordinates TensorAlgebra
universe u
variable {I : Type u}

def coordinates : L1 I →ₗ[ℝ] (I → ℝ) where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinates_injective : Function.Injective (coordinates (I := I)) := by
  intro x y h
  ext i
  exact congrFun h i

theorem independent_coordinates {r : ℕ} (a : Fin r → L1 I)
    (ha : LinearIndependent ℝ a) : LinearIndependent ℝ (fun t i => a t i) := by
  exact ha.map' coordinates (LinearMap.ker_eq_bot.mpr coordinates_injective)

def rowSpace (R : MatrixL1 I I) : Submodule ℝ (L1 I) :=
  Submodule.span ℝ (range (fun i => L1Coordinates.row i R))

theorem row_mem_rowSpace (R : MatrixL1 I I) (i : I) : L1Coordinates.row i R ∈ rowSpace R :=
  Submodule.subset_span (mem_range_self i)

theorem rowSpace_zero : rowSpace (0 : MatrixL1 I I) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change L1Coordinates.row i (0 : MatrixL1 I I) ∈ (⊥ : Submodule ℝ (L1 I))
  simp

theorem rowSpace_add_le (R Q : MatrixL1 I I) : rowSpace (R+Q) ≤ rowSpace R ⊔ rowSpace Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change L1Coordinates.row i (R+Q) ∈ rowSpace R ⊔ rowSpace Q
  rw [map_add]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (row_mem_rowSpace R i)) (Submodule.mem_sup_right (row_mem_rowSpace Q i))

theorem rowSpace_smul_le (c : ℝ) (R : MatrixL1 I I) : rowSpace (c • R) ≤ rowSpace R := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change L1Coordinates.row i (c • R) ∈ rowSpace R
  rw [map_smul]
  exact Submodule.smul_mem _ _ (row_mem_rowSpace R i)

theorem finiteDimensional_rowSpace {R : MatrixL1 I I} (hR : R ∈ algebraicSpan) :
    FiniteDimensional ℝ (rowSpace R) := by
  induction hR using Submodule.span_induction with
  | mem R hR =>
    obtain ⟨⟨a,b⟩,rfl⟩ := hR
    let W := Submodule.span ℝ ({b} : Set (L1 I))
    have hW : rowSpace (outer a b) ≤ W := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change L1Coordinates.row i (outer a b) ∈ W
      rw [row_outer]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_singleton b))
    letI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (finite_singleton b)
    exact Submodule.finiteDimensional_of_le hW
  | zero => rw [rowSpace_zero]; infer_instance
  | add x y hx hy IHx IHy =>
    letI := IHx
    letI := IHy
    exact Submodule.finiteDimensional_of_le (rowSpace_add_le x y)
  | smul a x hx IH =>
    letI := IH
    exact Submodule.finiteDimensional_of_le (rowSpace_smul_le a x)

theorem finiteDimensional_coordinate_columnSpace {R : MatrixL1 I I} (hR : R ∈ algebraicSpan) :
    FiniteDimensional ℝ (columnSpace (fun i j => R (i,j))) := by
  induction hR using Submodule.span_induction with
  | mem R hR =>
    obtain ⟨⟨a,b⟩,rfl⟩ := hR
    let W := Submodule.span ℝ ({fun i => a i} : Set (I → ℝ))
    have hW : columnSpace (fun i j => outer a b (i,j)) ≤ W := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      have ha : (fun i => a i) ∈ W := Submodule.subset_span (by simp)
      convert W.smul_mem (b j) ha using 1
      funext i
      simp [mul_comm]
    letI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (finite_singleton _)
    exact Submodule.finiteDimensional_of_le hW
  | zero =>
    change FiniteDimensional ℝ (columnSpace (fun (_ : I) (_ : I) => (0:ℝ)))
    rw [columnSpace_zero]
    infer_instance
  | add x y hx hy IHx IHy =>
    letI := IHx
    letI := IHy
    exact Submodule.finiteDimensional_of_le
      (columnSpace_add_le (fun i j => x (i,j)) (fun i j => y (i,j)))
  | smul a x hx IH =>
    letI := IH
    exact Submodule.finiteDimensional_of_le (columnSpace_smul_le a (fun i j => x (i,j)))

theorem exists_row_basis {R : MatrixL1 I I} (hR : R ∈ algebraicSpan) :
    ∃ r : ℕ, ∃ rows : Fin r → I,
      LinearIndependent ℝ (fun t => L1Coordinates.row (rows t) R) ∧
      Submodule.span ℝ (range (fun t => L1Coordinates.row (rows t) R)) = rowSpace R := by
  letI := finiteDimensional_rowSpace hR
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℝ (fun i => L1Coordinates.row i R)
  letI : FiniteDimensional ℝ (Submodule.span ℝ (range ((fun i => L1Coordinates.row i R) ∘ a))) :=
    hspan.symm ▸ finiteDimensional_rowSpace hR
  letI : Fintype κ := FiniteDimensional.fintypeBasisIndex (Module.Basis.span hli)
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ,a ∘ e,hli.comp e e.injective,?_⟩
  have hr : range (fun t => L1Coordinates.row ((a ∘ e) t) R) = range ((fun i => L1Coordinates.row i R) ∘ a) := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩; exact ⟨e t,rfl⟩
    · rintro ⟨k,rfl⟩
      obtain ⟨t,rfl⟩ := e.surjective k
      exact ⟨t,rfl⟩
  rw [hr]
  exact hspan

/-- Independent first tensor factors allow recovery of every second factor
from finitely many rows, using a nonsingular coordinate minor. -/
theorem factor_mem_rowSpace {r : ℕ} (x y : Fin r → L1 I)
    (hx : LinearIndependent ℝ (fun t i => x t i)) (t : Fin r) :
    y t ∈ rowSpace (∑ s, outer (x s) (y s)) := by
  classical
  obtain ⟨qs,hdet⟩ := exists_coordinate_pivot (fun t i => x t i) hx
  let N : Matrix (Fin r) (Fin r) ℝ := fun j i => x i (qs j)
  let R := ∑ s, outer (x s) (y s)
  have hrec : N.det • y t = ∑ j, N.adjugate t j • L1Coordinates.row (qs j) R := by
    ext k
    change (lp.evalCLM ℝ (fun _ : I => ℝ) 1 k) (N.det • y t) =
      (lp.evalCLM ℝ (fun _ : I => ℝ) 1 k) (∑ j, N.adjugate t j • L1Coordinates.row (qs j) R)
    simp only [map_smul,map_sum,smul_eq_mul]
    change N.det * y t k = ∑ j, N.adjugate t j * R (qs j,k)
    have hr (j : Fin r) : R (qs j,k) = (N *ᵥ (fun s => y s k)) j := by
      change (lp.evalCLM ℝ (fun _ : I×I => ℝ) 1 (qs j,k)) R = _
      simp only [R,map_sum,outer_apply,Matrix.mulVec,dotProduct,N]
      rfl
    simp_rw [hr]
    change N.det * y t k = (N.adjugate *ᵥ (N *ᵥ (fun s => y s k))) t
    rw [Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec]
    rfl
  have hh : N.det • y t ∈ rowSpace R := by
    rw [hrec]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (row_mem_rowSpace R (qs j)))
  exact (Submodule.smul_mem_iff _ hdet).mp hh

theorem exists_independent_decomposition {K : MatrixL1 I I} (hK : K ∈ algebraicSpan) :
    ∃ r : ℕ, ∃ x y : Fin r → L1 I,
      LinearIndependent ℝ (fun t i => x t i) ∧ K = ∑ t, outer (x t) (y t) := by
  classical
  letI := finiteDimensional_coordinate_columnSpace hK
  obtain ⟨r,cols,hli,hspan⟩ := exists_column_basis (fun i j => K (i,j))
  obtain ⟨rows,hdet⟩ := exists_coordinate_pivot (fun t i => K (i,cols t)) hli
  let P : Matrix (Fin r) (Fin r) ℝ := fun s t => K (rows s,cols t)
  let x : Fin r → L1 I := fun t => col (cols t) K
  let b : Fin r → L1 I := fun t => ∑ s, P.adjugate t s • L1Coordinates.row (rows s) K
  have hscaled : P.det • K = ∑ t, outer (x t) (b t) := by
    ext p
    change (lp.evalCLM ℝ (fun _ : I×I => ℝ) 1 p) (P.det • K) =
      (lp.evalCLM ℝ (fun _ : I×I => ℝ) 1 p) (∑ t, outer (x t) (b t))
    simp only [map_smul,map_sum,smul_eq_mul]
    change P.det * K p = ∑ t, x t p.1 * b t p.2
    have hrec := pivot_reconstruction (fun i j => K (i,j)) cols rows
      (fun j => by rw [hspan]; exact Submodule.subset_span (mem_range_self j)) p.1 p.2
    apply hrec.trans
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    change (∑ s, K (p.1,cols t) * (P.adjugate t s * K (rows s,p.2))) = _
    change _ = K (p.1,cols t) *
      (lp.evalCLM ℝ (fun _ : I => ℝ) 1 p.2) (∑ s, P.adjugate t s • L1Coordinates.row (rows s) K)
    simp only [map_sum,map_smul,smul_eq_mul]
    rw [Finset.mul_sum]
    rfl
  refine ⟨r,x,fun t => P.det⁻¹ • b t,hli,?_⟩
  calc
    K = P.det⁻¹ • (P.det • K) := by rw [smul_smul,inv_mul_cancel₀ hdet,one_smul]
    _ = ∑ t, outer (x t) (P.det⁻¹ • b t) := by
      rw [hscaled,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro t _
      exact (outer_smul_right P.det⁻¹ (x t) (b t)).symm

theorem mapLeft_mem_algebraicSpan (D : L1 I →L[ℝ] L1 I) {K : MatrixL1 I I}
    (hK : K ∈ algebraicSpan) : mapLeft D K ∈ algebraicSpan := by
  induction hK using Submodule.span_induction with
  | mem K hK => obtain ⟨⟨a,b⟩,rfl⟩ := hK; simpa using outer_mem (D a) b
  | zero => simpa using (algebraicSpan (I := I)).zero_mem
  | add x y hx hy IHx IHy => simpa only [map_add] using Submodule.add_mem _ IHx IHy
  | smul a x hx IH => simpa only [map_smul] using Submodule.smul_mem _ a IH

/-- An injective action on the first tensor factor preserves the entire
finite-dimensional row space. This direction is the recovery needed below. -/
theorem rowSpace_le_rowSpace_mapLeft (D : L1 I →L[ℝ] L1 I) (hD : Function.Injective D)
    {K : MatrixL1 I I} (hK : K ∈ algebraicSpan) : rowSpace K ≤ rowSpace (mapLeft D K) := by
  classical
  obtain ⟨r,x,y,hx,hxy⟩ := exists_independent_decomposition hK
  have hxnative : LinearIndependent ℝ x := by
    apply (coordinates.linearIndependent_iff (LinearMap.ker_eq_bot.mpr coordinates_injective)).mp
    exact hx
  have hxD := independent_coordinates (fun t => D (x t))
    (hxnative.map' D.toLinearMap (LinearMap.ker_eq_bot.mpr hD))
  have hR : mapLeft D K = ∑ t, outer (D (x t)) (y t) := by
    rw [hxy,map_sum]
    simp only [mapLeft_outer]
  have hy (t : Fin r) : y t ∈ rowSpace (mapLeft D K) := by
    rw [hR]
    exact factor_mem_rowSpace (fun t => D (x t)) y hxD t
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change L1Coordinates.row i K ∈ rowSpace (mapLeft D K)
  have hrow : L1Coordinates.row i K = ∑ t, (x t i) • y t := by
    rw [hxy]
    simp only [map_sum,row_outer]
  rw [hrow]
  exact Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (hy t))

end NoBorelUpperBoundFSigma.SymmetricTensor

end
end
-- END COMPLETE MODULE NoBorelUpperBound.SymmetricTensorRank

-- BEGIN COMPLETE MODULE NoBorelUpperBound.SymmetricTensorImage
section
                                              
                                            

noncomputable section
open Set Matrix
open scoped BigOperators

namespace NoBorelUpperBoundFSigma.SymmetricTensor
open L1Coordinates TensorAlgebra
universe u
variable {I : Type u}

theorem reconstruction_from_image {r : ℕ} (D : L1 I →L[ℝ] L1 I)
    (a : Fin r → L1 I) (qs : Fin r → I) (K : MatrixL1 I I)
    (hcol : ∀ j, L1Coordinates.col j K ∈ Submodule.span ℝ (range a)) (i j : I) :
    Matrix.det (fun s t => D (a t) (qs s)) * K (i,j) =
      (fun t => a t i) ⬝ᵥ
        ((Matrix.adjugate (fun s t => D (a t) (qs s))) *ᵥ
          (fun s => mapLeft D K (qs s,j))) := by
  classical
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hcol j)
  have heq (k : I) : ∑ t, c t * a t k = K (k,j) := by
    have h := congrArg (lp.evalCLM ℝ (fun _ : I => ℝ) 1 k) hc
    simpa only [map_sum,map_smul,smul_eq_mul] using h
  have hvec : (fun s => mapLeft D K (qs s,j)) =
      (fun s t => D (a t) (qs s)) *ᵥ c := by
    funext s
    change D (L1Coordinates.col j K) (qs s) = _
    rw [← hc,map_sum]
    change (lp.evalCLM ℝ (fun _ : I => ℝ) 1 (qs s)) (∑ t, D (c t • a t)) = _
    simp only [map_sum,map_smul,smul_eq_mul,Matrix.mulVec,dotProduct]
    apply Finset.sum_congr rfl
    intro t _
    change c t * D (a t) (qs s) = D (a t) (qs s) * c t
    ring
  rw [hvec,Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,
    Matrix.one_mulVec,dotProduct_smul]
  congr 1
  simpa only [dotProduct,mul_comm] using (heq i).symm

theorem liftNumerator_apply (D : L1 I →L[ℝ] L1 I) {r : ℕ} (rows qs : Fin r → I)
    (R : MatrixL1 I I) (i j : I) :
    liftNumerator D rows qs R (i,j) =
      ∑ t, ∑ s, (pivotD D rows qs R).adjugate t s *
        (R (rows t,i) * R (qs s,j)) := by
  change (lp.evalCLM ℝ (fun _ : I×I => ℝ) 1 (i,j)) (liftNumerator D rows qs R) = _
  simp only [liftNumerator,map_sum,map_smul,smul_eq_mul]
  rfl

/-- Actual finite-row reconstruction of every member of the symmetric image. -/
theorem exists_imageChart_of_mem (D : L1 I →L[ℝ] L1 I) (hD : Function.Injective D)
    (o : I) {p : ℝ × MatrixL1 I I} (hp : p ∈ imageSubmodule D o) :
    ∃ r : ℕ, ∃ rows qs : Fin r → I, ∃ m : ℕ, p ∈ imageChart D o rows qs m := by
  classical
  obtain ⟨K,hK,rfl⟩ := hp
  let R := mapLeft D K
  have hKalg := symmetricSpan_le_algebraicSpan hK
  have hRalg : R ∈ algebraicSpan := mapLeft_mem_algebraicSpan D hKalg
  obtain ⟨r,rows,hli,hspan⟩ := exists_row_basis hRalg
  let a : Fin r → L1 I := fun t => L1Coordinates.row (rows t) R
  have hcol (j : I) : L1Coordinates.col j K ∈ Submodule.span ℝ (range a) := by
    change L1Coordinates.col j K ∈ Submodule.span ℝ (range (fun t => L1Coordinates.row (rows t) R))
    rw [hspan]
    have hc : L1Coordinates.col j K = L1Coordinates.row j K := by
      ext i
      exact symmetric_of_mem hK i j
    rw [hc]
    exact rowSpace_le_rowSpace_mapLeft D hD hKalg (row_mem_rowSpace K j)
  have hliD : LinearIndependent ℝ (fun t i => D (a t) i) :=
    independent_coordinates (fun t => D (a t))
      (hli.map' D.toLinearMap (LinearMap.ker_eq_bot.mpr hD))
  obtain ⟨qs,hdet⟩ := exists_coordinate_pivot (fun t i => D (a t) i) hliD
  have hscaled : (pivotD D rows qs R).det • K = liftNumerator D rows qs R := by
    ext ij
    change (pivotD D rows qs R).det * K ij = liftNumerator D rows qs R ij
    rw [show ij = (ij.1,ij.2) from rfl,liftNumerator_apply]
    apply (reconstruction_from_image D a qs K hcol ij.1 ij.2).trans
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro s _
    change (a t ij.1) * ((pivotD D rows qs R).adjugate t s * R (qs s,ij.2)) = _
    change R (rows t,ij.1) * ((pivotD D rows qs R).adjugate t s * R (qs s,ij.2)) = _
    ring
  have hd : (pivotD D rows qs R).det ≠ 0 := hdet
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt (abs_pos.mpr hd)
  refine ⟨r,rows,qs,m,hm.le,?_,?_,?_⟩
  · change (pivotD D rows qs R).det • R = mapLeft D (liftNumerator D rows qs R)
    rw [← hscaled,map_smul]
  · change L1Coordinates.transpose (liftNumerator D rows qs R) = liftNumerator D rows qs R
    rw [← hscaled,map_smul,transpose_eq_of_mem_symmetricSpan hK]
  · have h := congrArg (lp.evalCLM ℝ (fun _ : I×I => ℝ) 1 (o,o)) hscaled
    simpa only [map_smul,smul_eq_mul] using h

/-- Lemma 3: injectivity alone makes the scalar-tagged symmetric finite
tensor image an F-sigma real linear subspace of R times the matrix l1 space. -/
theorem isFSigma_imageSubmodule [Countable I]
    (D : L1 I →L[ℝ] L1 I) (hD : Function.Injective D) (o : I) :
    NoUniversalFSigma.IsFSigma (imageSubmodule D o : Set (ℝ × MatrixL1 I I)) :=
  isFSigma_image_of_chart_coverage D o (fun _ hp => exists_imageChart_of_mem D hD o hp)

end NoBorelUpperBoundFSigma.SymmetricTensor

end
end
-- END COMPLETE MODULE NoBorelUpperBound.SymmetricTensorImage

-- BEGIN COMPLETE MODULE NoBorelUpperBound.TreeSpace
section
                                                
                            
                                         
                             
                     

noncomputable section
open Set TopologicalSpace Topology

namespace NoBorelUpperBoundFSigma.Trees

abbrev Node := List ℕ
abbrev Baire := ℕ → ℕ

def TreeProperty (t : Node → Bool) : Prop :=
  ∀ s n, t (s ++ [n]) = true → t s = true

abbrev TreeSpace := {t : Node → Bool // TreeProperty t}

instance : CoeFun TreeSpace (fun _ => Node → Bool) := ⟨fun t => t.val⟩

theorem isClosed_treeProperty : IsClosed {t : Node → Bool | TreeProperty t} := by
  unfold TreeProperty
  simp only [setOf_forall]
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro n
  have heq : {t : Node → Bool | t (s ++ [n]) = true → t s = true} =
      {t | t (s ++ [n]) = false} ∪ {t | t s = true} := by
    ext t
    cases h : t (s ++ [n]) <;> simp [h]
  rw [heq]
  exact (isClosed_eq (continuous_apply (s ++ [n])) continuous_const).union
    (isClosed_eq (continuous_apply s) continuous_const)

instance : PolishSpace TreeSpace := by
  letI : PolishSpace (Node → Bool) :=
    { toSecondCountableTopology := inferInstance
      toIsCompletelyMetrizableSpace := inferInstance }
  exact isClosed_treeProperty.polishSpace
instance : CompactSpace TreeSpace := isCompact_iff_compactSpace.mp isClosed_treeProperty.isCompact

def mem (T : TreeSpace) (s : Node) : Prop := T s = true

theorem mem_parent (T : TreeSpace) (s : Node) (n : ℕ) (h : T (s ++ [n]) = true) :
    T s = true := T.property s n h

theorem mem_of_append (T : TreeSpace) (s t : Node) (h : T (s ++ t) = true) : T s = true := by
  induction t using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton t n ih =>
    exact ih (mem_parent T (s ++ t) n (by simpa only [List.append_assoc] using h))

def branchPrefix (x : Baire) (n : ℕ) : Node := List.ofFn (fun i : Fin n => x i)

@[simp] theorem length_branchPrefix (x : Baire) (n : ℕ) : (branchPrefix x n).length = n := by
  simp [branchPrefix]

@[simp] theorem branchPrefix_zero (x : Baire) : branchPrefix x 0 = [] := rfl

theorem branchPrefix_succ (x : Baire) (n : ℕ) : branchPrefix x (n + 1) = branchPrefix x n ++ [x n] := by
  simpa [branchPrefix, List.concat_eq_append] using List.ofFn_succ' (fun i : Fin (n + 1) => x i)

theorem continuous_branchPrefix (n : ℕ) : Continuous (fun x : Baire => branchPrefix x n) := by
  exact (continuous_of_discreteTopology : Continuous (List.ofFn : (Fin n → ℕ) → Node)).comp
    (continuous_pi (fun i => continuous_apply (i : ℕ)))

theorem continuous_eval (s : Node) : Continuous (fun T : TreeSpace => T s) :=
  (continuous_apply s).comp continuous_subtype_val

def HasBranch (T : TreeSpace) : Prop := ∃ x : Baire, ∀ n, T (branchPrefix x n) = true
def IF : Set TreeSpace := {T | HasBranch T}

def fullTree : TreeSpace := ⟨fun _ => true, fun _ _ _ => rfl⟩
def emptyTree : TreeSpace := ⟨fun _ => false, by simp [TreeProperty]⟩

theorem fullTree_mem_IF : fullTree ∈ IF := ⟨fun _ => 0, fun _ => rfl⟩
theorem emptyTree_not_mem_IF : emptyTree ∉ IF := by
  rintro ⟨x, hx⟩
  have h := hx 0
  cases h

end NoBorelUpperBoundFSigma.Trees

end
end
-- END COMPLETE MODULE NoBorelUpperBound.TreeSpace

-- BEGIN COMPLETE MODULE NoBorelUpperBound.TreeShift
section
                                      
                                                   

noncomputable section
open Set Filter Topology
open scoped BigOperators ENNReal

namespace NoBorelUpperBoundFSigma.TreeOperators
open L1Coordinates

abbrev Node := List ℕ
abbrev Space := L1 Node
abbrev Code := Node → Bool

def child (p : Node × ℕ) : Node := p.1 ++ [p.2]

theorem child_injective : Function.Injective child := by
  rintro ⟨s,n⟩ ⟨t,m⟩ h
  have hs : s = t := by simpa [child] using congrArg List.dropLast h
  subst t
  have hn : n = m := by simpa [child] using (List.append_cancel_left h)
  exact Prod.ext rfl hn

def summand (t : Code) (x : Space) (p : Node × ℕ) : Space :=
  lp.single 1 p.1 (if t (child p) = true then x (child p) else 0)

theorem norm_summand_le (t : Code) (x : Space) (p : Node × ℕ) :
    ‖summand t x p‖ ≤ ‖x (child p)‖ := by
  rw [summand, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]
  split_ifs <;> simp

theorem summable_envelope (x : Space) : Summable (fun p : Node × ℕ => ‖x (child p)‖) :=
  (summable_norm x).comp_injective child_injective

theorem summable_norm_summand (t : Code) (x : Space) :
    Summable (fun p => ‖summand t x p‖) :=
  (summable_envelope x).of_nonneg_of_le (fun _ => norm_nonneg _) (norm_summand_le t x)

theorem summable_summand (t : Code) (x : Space) : Summable (summand t x) :=
  (summable_norm_summand t x).of_norm

def shift (t : Code) (x : Space) : Space := ∑' p, summand t x p

theorem norm_shift_le (t : Code) (x : Space) : ‖shift t x‖ ≤ ‖x‖ := by
  calc
    ‖shift t x‖ ≤ ∑' p, ‖summand t x p‖ := norm_tsum_le_tsum_norm (summable_norm_summand t x)
    _ ≤ ∑' p : Node × ℕ, ‖x (child p)‖ :=
      (summable_norm_summand t x).tsum_le_tsum (norm_summand_le t x) (summable_envelope x)
    _ ≤ ∑' s, ‖x s‖ :=
      tsum_comp_le_tsum_of_inj (summable_norm x) (fun _ => norm_nonneg _) child_injective
    _ = ‖x‖ := (norm_eq_tsum x).symm

theorem summand_add (t : Code) (x y : Space) (p : Node × ℕ) :
    summand t (x+y) p = summand t x p + summand t y p := by
  unfold summand
  split_ifs
  · change (lp.single 1 p.1 (x (child p) + y (child p)) : Space) = _
    exact lp.single_add _ _ _ _
  · simp

theorem summand_smul (t : Code) (a : ℝ) (x : Space) (p : Node × ℕ) :
    summand t (a • x) p = a • summand t x p := by
  unfold summand
  split_ifs
  · change (lp.single 1 p.1 (a • x (child p)) : Space) = _
    exact lp.single_smul _ _ _ _
  · simp

def shiftCLM (t : Code) : Space →L[ℝ] Space :=
  ({toFun:=shift t
    map_add':=by
      intro x y
      simp only [shift,summand_add]
      exact (summable_summand t x).tsum_add (summable_summand t y)
    map_smul':=by
      intro a x
      simp only [shift,summand_smul,RingHom.id_apply]
      exact Summable.tsum_const_smul a (summable_summand t x)} : Space →ₗ[ℝ] Space).mkContinuous 1
    (fun x => by simpa using norm_shift_le t x)

@[simp] theorem shiftCLM_apply (t : Code) (x : Space) : shiftCLM t x = shift t x := rfl

theorem shift_apply (t : Code) (x : Space) (s : Node) :
    shift t x s = ∑' n, if t (s ++ [n]) = true then x (s ++ [n]) else 0 := by
  let ev : Space →L[ℝ] ℝ := lp.evalCLM ℝ (fun _ : Node => ℝ) 1 s
  have heval : Summable (fun p => ev (summand t x p)) :=
    (summable_summand t x).map ev.toAddMonoidHom ev.continuous
  change ev (∑' p, summand t x p) = _
  rw [ev.map_tsum (summable_summand t x), heval.tsum_prod, tsum_eq_single s]
  · apply tsum_congr
    intro n
    change (lp.single 1 s (if t (s ++ [n]) = true then x (s ++ [n]) else 0) : Space) s = _
    exact lp.single_apply_self _ _ _
  · intro u hu
    have heq (n : ℕ) : ev (summand t x (u,n)) = 0 := by
      change (lp.single 1 u _ : Space) s = (0 : ℝ)
      exact lp.single_apply_ne _ _ _ hu.symm
    simp only [heq,tsum_zero]

theorem continuous_summand (x : Space) (p : Node × ℕ) :
    Continuous (fun t : Code => summand t x p) := by
  have hb : Continuous (fun b : Bool => if b = true then x (child p) else 0) :=
    continuous_of_discreteTopology
  exact (lp.singleContinuousLinearMap ℝ (fun _ : Node => ℝ) 1 p.1).continuous.comp
    (hb.comp (continuous_apply (child p)))

theorem continuous_shift_fixed (x : Space) : Continuous (fun t : Code => shift t x) :=
  continuous_tsum (continuous_summand x) (summable_envelope x) (fun p t => norm_summand_le t x p)

theorem continuous_shift : Continuous (fun p : Code × Space => shift p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hnorm : Tendsto (fun q : Code × Space => ‖q.2-p.2‖) (𝓝 p) (𝓝 0) := by
    simpa only [sub_self,norm_zero] using
      (((continuous_snd.tendsto p).sub
        (tendsto_const_nhds : Tendsto (fun _ : Code × Space => p.2) (𝓝 p) (𝓝 p.2))).norm)
  have hzero : Tendsto (fun q : Code × Space => shift q.1 (q.2-p.2)) (𝓝 p) (𝓝 0) :=
    squeeze_zero_norm (fun q => norm_shift_le q.1 (q.2-p.2)) hnorm
  have hfixed : Tendsto (fun q : Code × Space => shift q.1 p.2) (𝓝 p) (𝓝 (shift p.1 p.2)) :=
    ((continuous_shift_fixed p.2).tendsto p.1).comp (continuous_fst.tendsto p)
  have heq (q : Code × Space) : shift q.1 (q.2-p.2) + shift q.1 p.2 = shift q.1 q.2 := by
    change shiftCLM q.1 (q.2-p.2) + shiftCLM q.1 p.2 = _
    rw [← map_add,sub_add_cancel,shiftCLM_apply]
  simpa only [zero_add] using (hzero.add hfixed).congr' (Eventually.of_forall heq)

def operator (t : Code) : Space →L[ℝ] Space := ContinuousLinearMap.id ℝ Space - (2 : ℝ) • shiftCLM t

theorem continuous_operator : Continuous (fun p : Code × Space => operator p.1 p.2) := by
  exact continuous_snd.sub (continuous_shift.const_smul (2 : ℝ))

theorem norm_operator_le (t : Code) (x : Space) : ‖operator t x‖ ≤ 3 * ‖x‖ := by
  change ‖x - (2 : ℝ) • shift t x‖ ≤ _
  calc
    ‖x - (2 : ℝ) • shift t x‖ ≤ ‖x‖ + ‖(2 : ℝ) • shift t x‖ := norm_sub_le _ _
    _ = ‖x‖ + 2 * ‖shift t x‖ := by rw [norm_smul]; norm_num
    _ ≤ 3 * ‖x‖ := by nlinarith [norm_shift_le t x]

theorem shift_single_nil (t : Code) (a : ℝ) :
    shift t (lp.single 1 ([] : Node) a) = 0 := by
  have heq (p : Node × ℕ) : summand t (lp.single 1 ([] : Node) a) p = 0 := by
    have hp : child p ≠ [] := by simp [child]
    simp only [summand,lp.single_apply_ne _ _ _ hp]
    split_ifs <;> simp
  simp only [shift,heq,tsum_zero]

theorem shift_single_concat (t : Code) (s : Node) (n : ℕ) (a : ℝ) :
    shift t (lp.single 1 (s++[n]) a) =
      if t (s++[n]) = true then lp.single 1 s a else 0 := by
  rw [shift,tsum_eq_single (s,n)]
  · simp only [summand,child,lp.single_apply_self]
    split_ifs <;> simp
  · intro p hp
    have hn : child p ≠ s++[n] := fun h => hp (child_injective h)
    simp only [summand,lp.single_apply_ne _ _ _ hn]
    split_ifs <;> simp

@[simp] theorem operator_apply (t : Code) (x : Space) (s : Node) :
    operator t x s = x s - 2 * ∑' n, if t (s ++ [n]) = true then x (s ++ [n]) else 0 := by
  change x s - 2 * shift t x s = _
  rw [shift_apply]

theorem operator_eq_zero_iff (t : Code) (x : Space) :
    operator t x = 0 ↔ ∀ s, x s = 2 * ∑' n, if t (s ++ [n]) = true then x (s ++ [n]) else 0 := by
  constructor
  · intro h s
    have h' := congrArg (fun y : Space => y s) h
    simpa only [operator_apply,lp.coeFn_zero,Pi.zero_apply,sub_eq_zero] using h'
  · intro h
    ext s
    simpa only [operator_apply,lp.coeFn_zero,Pi.zero_apply,sub_eq_zero] using h s

end NoBorelUpperBoundFSigma.TreeOperators

end
end
-- END COMPLETE MODULE NoBorelUpperBound.TreeShift

-- BEGIN COMPLETE MODULE NoBorelUpperBound.TreeKernels
section
                                  
                                  
                                             

noncomputable section
open Set Filter Topology
open scoped BigOperators ENNReal

namespace NoBorelUpperBoundFSigma.TreeOperators
open L1Coordinates Trees

def branchSummand (b : Baire) (n : ℕ) : Space :=
  lp.single 1 (branchPrefix b n) ((1/2 : ℝ)^n)

theorem norm_branchSummand (b : Baire) (n : ℕ) : ‖branchSummand b n‖ = (1/2 : ℝ)^n := by
  rw [branchSummand,lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]
  simp only [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1/2 : ℝ)^n)]

theorem summable_branchSummand (b : Baire) : Summable (branchSummand b) := by
  apply Summable.of_norm
  simpa only [norm_branchSummand] using
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1))

def branchVector (b : Baire) : Space := ∑' n, branchSummand b n

theorem branchVector_root (b : Baire) : branchVector b [] = 1 := by
  let ev : Space →L[ℝ] ℝ := lp.evalCLM ℝ (fun _ : Node => ℝ) 1 []
  change ev (∑' n, branchSummand b n) = _
  rw [ev.map_tsum (summable_branchSummand b),tsum_eq_single 0]
  · change (lp.single 1 (branchPrefix b 0) ((1/2 : ℝ)^0) : Space) [] = 1
    simp only [branchPrefix_zero,pow_zero,lp.single_apply_self]
  · intro n hn
    have hne : ([] : Node) ≠ branchPrefix b n := by
      intro h
      have hh := congrArg List.length h
      simp only [List.length_nil,length_branchPrefix] at hh
      exact hn hh.symm
    change (lp.single 1 (branchPrefix b n) ((1/2 : ℝ)^n) : Space) [] = 0
    exact lp.single_apply_ne _ _ _ hne

theorem shift_branchVector (T : TreeSpace) (b : Baire)
    (hb : ∀ n, T (branchPrefix b n) = true) :
    shift T (branchVector b) = (1/2 : ℝ) • branchVector b := by
  change shiftCLM T (∑' n, branchSummand b n) = _
  rw [(shiftCLM T).map_tsum (summable_branchSummand b)]
  have hm : Summable (fun n => shiftCLM T (branchSummand b n)) :=
    (summable_branchSummand b).map (shiftCLM T) (shiftCLM T).continuous
  rw [hm.tsum_eq_zero_add]
  have hz : shiftCLM T (branchSummand b 0) = 0 := by
    simp only [branchSummand,branchPrefix_zero,shiftCLM_apply,shift_single_nil]
  rw [hz,zero_add]
  have hs (n : ℕ) : shiftCLM T (branchSummand b (n+1)) = (1/2 : ℝ) • branchSummand b n := by
    rw [shiftCLM_apply,branchSummand,branchPrefix_succ,shift_single_concat]
    rw [← branchPrefix_succ,hb,if_pos rfl]
    rw [branchSummand,pow_succ,mul_comm,← smul_eq_mul,lp.single_smul]
  simp_rw [hs]
  exact Summable.tsum_const_smul _ (summable_branchSummand b)

theorem operator_branchVector (T : TreeSpace) (b : Baire)
    (hb : ∀ n, T (branchPrefix b n) = true) : operator T (branchVector b) = 0 := by
  change branchVector b - (2 : ℝ) • shift T (branchVector b) = 0
  rw [shift_branchVector T b hb,smul_smul]
  norm_num

theorem exists_nonzero_child (t : Code) (x : Space) (hx : operator t x = 0)
    (s : Node) (hs : x s ≠ 0) : ∃ n, t (s++[n]) = true ∧ x (s++[n]) ≠ 0 := by
  classical
  by_contra! h
  have heq (n : ℕ) : (if t (s++[n]) = true then x (s++[n]) else 0) = 0 := by
    split_ifs with hn
    · exact h n hn
    · rfl
  have hr := (operator_eq_zero_iff t x).mp hx s
  simp only [heq,tsum_zero,mul_zero] at hr
  exact hs hr

def nextDigit (t : Code) (x : Space) (hx : operator t x = 0) (s : Node) : ℕ :=
  if hs : x s ≠ 0 then Classical.choose (exists_nonzero_child t x hx s hs) else 0

theorem nextDigit_good (t : Code) (x : Space) (hx : operator t x = 0)
    (s : Node) (hs : x s ≠ 0) :
    t (s++[nextDigit t x hx s]) = true ∧ x (s++[nextDigit t x hx s]) ≠ 0 := by
  simpa only [nextDigit,dif_pos hs] using Classical.choose_spec (exists_nonzero_child t x hx s hs)

def nodeChain (t : Code) (x : Space) (hx : operator t x = 0) (s : Node) : ℕ → Node
  | 0 => s
  | n+1 => nodeChain t x hx s n ++ [nextDigit t x hx (nodeChain t x hx s n)]

theorem nodeChain_nonzero (t : Code) (x : Space) (hx : operator t x = 0)
    (s : Node) (hs : x s ≠ 0) (n : ℕ) : x (nodeChain t x hx s n) ≠ 0 := by
  induction n with
  | zero => exact hs
  | succ n IH => exact (nextDigit_good t x hx _ IH).2

def tailDigits (t : Code) (x : Space) (hx : operator t x = 0) (s : Node) : Baire :=
  fun n => nextDigit t x hx (nodeChain t x hx s n)

theorem nodeChain_eq (t : Code) (x : Space) (hx : operator t x = 0) (s : Node) (n : ℕ) :
    nodeChain t x hx s n = s ++ branchPrefix (tailDigits t x hx s) n := by
  induction n with
  | zero => simp [nodeChain]
  | succ n IH =>
    rw [nodeChain,IH,branchPrefix_succ,List.append_assoc]
    simp only [tailDigits,IH]

def extendDigits (s : Node) (b : Baire) : Baire :=
  fun n => if h : n < s.length then s[n] else b (n-s.length)

theorem branchPrefix_extendDigits (s : Node) (b : Baire) (n : ℕ) :
    branchPrefix (extendDigits s b) (s.length+n) = s ++ branchPrefix b n := by
  induction n with
  | zero =>
    simp only [Nat.add_zero,branchPrefix_zero,List.append_nil]
    change List.ofFn (fun i : Fin s.length => extendDigits s b i) = s
    simpa [extendDigits] using List.ofFn_get s
  | succ n IH =>
    rw [Nat.add_succ,branchPrefix_succ,IH,branchPrefix_succ,List.append_assoc]
    congr 2
    simp [extendDigits]

theorem branchPrefix_add (b : Baire) (n m : ℕ) :
    branchPrefix b (n+m) = branchPrefix b n ++ branchPrefix (fun k => b (n+k)) m := by
  simpa [branchPrefix] using (List.ofFn_add (f := fun i : Fin (n+m) => b i))

theorem hasBranch_of_kernel_nonzero (T : TreeSpace) (x : Space)
    (hx : operator T x = 0) (hne : x ≠ 0) : HasBranch T := by
  classical
  have hex : ∃ s, x s ≠ 0 := by
    by_contra! h
    exact hne (by ext s; exact h s)
  obtain ⟨s,hs⟩ := hex
  let b := extendDigits s (tailDigits T x hx s)
  have hchain (n : ℕ) : T (nodeChain T x hx s n) = true :=
    mem_parent T _ _ (nextDigit_good T x hx _ (nodeChain_nonzero T x hx s hs n)).1
  refine ⟨b,fun n => ?_⟩
  have heq : nodeChain T x hx s n = branchPrefix b (n+s.length) := by
    rw [Nat.add_comm,branchPrefix_extendDigits,nodeChain_eq]
  have hc := hchain n
  rw [heq,branchPrefix_add] at hc
  exact mem_of_append T _ _ hc

theorem hasBranch_iff_exists_kernel_root (T : TreeSpace) :
    HasBranch T ↔ ∃ x : Space, operator T x = 0 ∧ x [] = 1 := by
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨branchVector b,operator_branchVector T b hb,branchVector_root b⟩
  · rintro ⟨x,hx,hr⟩
    apply hasBranch_of_kernel_nonzero T x hx
    intro hzero
    rw [hzero] at hr
    change (0 : ℝ) = 1 at hr
    norm_num at hr

theorem operator_injective_of_not_hasBranch (T : TreeSpace) (hT : ¬ HasBranch T) :
    Function.Injective (operator T) := by
  intro x y hxy
  by_contra hne
  have hz : operator T (x-y) = 0 := by rw [map_sub,hxy,sub_self]
  exact hT (hasBranch_of_kernel_nonzero T (x-y) hz (sub_ne_zero.mpr hne))

end NoBorelUpperBoundFSigma.TreeOperators

end
end
-- END COMPLETE MODULE NoBorelUpperBound.TreeKernels

-- BEGIN COMPLETE MODULE NoBorelUpperBound.L1Separable
section
                                      
                                            

noncomputable section
open Set Filter TopologicalSpace Topology
open scoped BigOperators ENNReal

namespace NoBorelUpperBoundFSigma.L1Coordinates
universe u

instance {I : Type u} [Countable I] : SeparableSpace (L1 I) := by
  classical
  let S : Submodule ℝ (L1 I) := Submodule.span ℝ (range (fun i : I => lp.single 1 i (1 : ℝ)))
  have hs : IsSeparable (S : Set (L1 I)) := (countable_range _).isSeparable.span
  have hd : closure (S : Set (L1 I)) = univ := by
    apply eq_univ_of_forall
    intro x
    apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) x)
    apply Eventually.of_forall
    intro s
    apply subset_closure
    apply Submodule.sum_mem S
    intro i _
    have heq : (lp.single 1 i (x i) : L1 I) = (x i) • (lp.single 1 i (1 : ℝ) : L1 I) := by
      ext j
      by_cases h : j = i
      · subst j; simp
      · simp [lp.single_apply, h]
    rw [heq]
    exact S.smul_mem (x i) (Submodule.subset_span (mem_range_self i))
  have h := hs.closure
  rw [hd] at h
  exact isSeparable_univ_iff.mp h

end NoBorelUpperBoundFSigma.L1Coordinates

end
end
-- END COMPLETE MODULE NoBorelUpperBound.L1Separable

-- BEGIN COMPLETE MODULE NoBorelUpperBound.Construction
section
                                           
                                        
                                             
                                    
                                    
                                            
                                           

noncomputable section
open Set Topology

namespace NoBorelUpperBoundFSigma.Construction
open L1Coordinates SymmetricTensor TreeOperators Trees

abbrev A := TreeOperators.Space
abbrev Z := MatrixL1 Trees.Node Trees.Node
abbrev X := A × A
abbrev C := ℝ × Z

def rootEval : X →L[ℝ] ℝ :=
  (lp.evalCLM ℝ (fun _ : Trees.Node => ℝ) 1 []).comp (ContinuousLinearMap.fst ℝ A A)

def scalarBeta : X →L[ℝ] X →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp rootEval rootEval

def tensorBeta : X →L[ℝ] X →L[ℝ] Z :=
  (1/2 : ℝ) • ((outerBilinear.bilinearComp
    (ContinuousLinearMap.snd ℝ A A) (ContinuousLinearMap.fst ℝ A A)) +
    (outerBilinear.flip.bilinearComp
      (ContinuousLinearMap.fst ℝ A A) (ContinuousLinearMap.snd ℝ A A)))

def beta : X →L[ℝ] X →L[ℝ] C :=
  (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := X) (F := ℝ) (G := Z) ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (scalarBeta.prod tensorBeta)

@[simp] theorem beta_apply (x y : X) :
    beta x y = (x.1 [] * y.1 [],(1/2 : ℝ) • (outer x.2 y.1 + outer y.2 x.1)) := rfl

abbrev G := CentralExtension beta

instance : PolishSpace A := by infer_instance
instance : PolishSpace Z := by infer_instance
instance : PolishSpace G := by infer_instance

def graphMap (D : A →L[ℝ] A) : A →L[ℝ] X := (ContinuousLinearMap.id ℝ A).prod D

@[simp] theorem graphMap_apply (D : A →L[ℝ] A) (a : A) : graphMap D a = (a,D a) := rfl

theorem isClosed_range_graphMap (D : A →L[ℝ] A) : IsClosed ((graphMap D).range : Set X) := by
  have heq : ((graphMap D).range : Set X) = {x | x.2 = D x.1} := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      rfl
    · intro h
      exact ⟨x.1,Prod.ext rfl h.symm⟩
  rw [heq]
  exact isClosed_eq continuous_snd (D.continuous.comp continuous_fst)

@[simp] theorem beta_graph (D : A →L[ℝ] A) (a b : A) :
    beta (graphMap D a) (graphMap D b) = imageMap D [] (sym a b) := by
  apply Prod.ext
  · rw [beta_apply]
    change a [] * b [] = (sym a b) ([],[])
    change a [] * b [] = (1/2 : ℝ) * (a [] * b [] + b [] * a [])
    ring
  · rw [beta_apply]
    exact (mapLeft_sym D a b).symm

theorem centralSpan_eq_imageSubmodule (D : A →L[ℝ] A) :
    CentralExtension.centralSpan beta (graphMap D) = imageSubmodule D [] := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro c ⟨⟨a,b⟩,rfl⟩
    change beta (graphMap D a) (graphMap D b) ∈ imageSubmodule D []
    rw [beta_graph]
    exact ⟨sym a b,sym_mem a b,rfl⟩
  · rintro c ⟨K,hK,rfl⟩
    induction hK using Submodule.span_induction with
    | mem K hK =>
      obtain ⟨⟨a,b⟩,rfl⟩ := hK
      change imageMap D [] (sym a b) ∈ CentralExtension.centralSpan beta (graphMap D)
      rw [← beta_graph]
      exact CentralExtension.beta_mem_centralSpan beta (graphMap D) a b
    | zero =>
      change imageMap D [] 0 ∈ CentralExtension.centralSpan beta (graphMap D)
      rw [map_zero]
      exact (CentralExtension.centralSpan beta (graphMap D)).zero_mem
    | add K L hK hL IHK IHL =>
      simpa using (CentralExtension.centralSpan beta (graphMap D)).add_mem IHK IHL
    | smul r K hK IH =>
      simpa using (CentralExtension.centralSpan beta (graphMap D)).smul_mem r IH

def subgroup (D : A →L[ℝ] A) : Subgroup G := CentralExtension.generatedAxes beta (graphMap D)

def cosetSetoid (D : A →L[ℝ] A) : Setoid G where
  r := GroupCosetRelation (subgroup D)
  iseqv := ⟨by intro g; simpa only [GroupCosetRelation,inv_mul_cancel] using (subgroup D).one_mem,
    by
      intro g h hgh
      have hi := (subgroup D).inv_mem hgh
      simpa only [GroupCosetRelation,mul_inv_rev,inv_inv] using hi,
    by
      intro g h k hgh hhk
      have hm := (subgroup D).mul_mem hgh hhk
      simpa only [GroupCosetRelation,mul_assoc,mul_inv_cancel_left] using hm⟩

def designated : G := CentralExtension.center beta (1,0)

theorem designated_mem_iff (D : A →L[ℝ] A) :
    designated ∈ subgroup D ↔ ∃ a : A, D a = 0 ∧ a [] = 1 := by
  rw [subgroup,CentralExtension.generatedAxes_eq_coordinateSubgroup]
  change (0 ∈ (graphMap D).range ∧ 0 ∈ (graphMap D).range ∧
    (1,0) ∈ CentralExtension.centralSpan beta (graphMap D)) ↔ _
  rw [centralSpan_eq_imageSubmodule]
  simp only [Submodule.zero_mem,true_and]
  constructor
  · rintro ⟨K,hK,himage⟩
    have hr : K ([],[]) = 1 := congrArg Prod.fst himage
    have hD : mapLeft D K = 0 := congrArg Prod.snd himage
    refine ⟨col [] K,?_,hr⟩
    ext i
    have h := congrArg (fun R : Z => R (i,[])) hD
    exact h
  · rintro ⟨a,hDa,ha⟩
    refine ⟨sym a a,sym_mem a a,?_⟩
    apply Prod.ext
    · change (sym a a) ([],[]) = 1
      change (1/2 : ℝ) * (a [] * a [] + a [] * a []) = 1
      rw [ha]
      norm_num
    · simp [hDa]

theorem designated_mem_tree_iff (T : TreeSpace) :
    designated ∈ subgroup (operator T) ↔ HasBranch T := by
  rw [designated_mem_iff,hasBranch_iff_exists_kernel_root]

theorem isFSigma_subgroup (D : A →L[ℝ] A) (hD : Function.Injective D) :
    NoUniversalFSigma.IsFSigma (subgroup D : Set G) := by
  apply CentralExtension.isFSigma_generatedAxes beta (graphMap D) (isClosed_range_graphMap D)
  rw [centralSpan_eq_imageSubmodule]
  exact isFSigma_imageSubmodule D hD []

theorem isFSigma_tree_subgroup (T : TreeSpace) (hT : ¬ HasBranch T) :
    NoUniversalFSigma.IsFSigma (subgroup (operator T) : Set G) :=
  isFSigma_subgroup _ (operator_injective_of_not_hasBranch T hT)

theorem isFSigma_cosetGraph (D : A →L[ℝ] A) (hD : Function.Injective D) :
    NoUniversalFSigma.IsFSigma {p : G × G | GroupCosetRelation (subgroup D) p.1 p.2} := by
  obtain ⟨F,hF,hcover⟩ := isFSigma_subgroup D hD
  refine ⟨fun n => (fun p : G×G => p.1⁻¹*p.2) ⁻¹' F n,?_,?_⟩
  · intro n
    exact (hF n).preimage (continuous_fst.inv.mul continuous_snd)
  · change (fun p : G×G => p.1⁻¹*p.2) ⁻¹' (subgroup D : Set G) = _
    rw [hcover,preimage_iUnion]

end NoBorelUpperBoundFSigma.Construction

end
end
-- END COMPLETE MODULE NoBorelUpperBound.Construction

-- BEGIN COMPLETE MODULE ModNullProof.TensorFamily
section
                               
                                     

set_option autoImplicit false
noncomputable section

namespace ModNullUniversality.CompactTensor

def oldTree (T : WF) : NoBorelUpperBoundFSigma.Trees.TreeSpace :=
  ⟨T.val.val,T.val.property⟩

def treeOperator (T : WF) :
    NoBorelUpperBoundFSigma.L1Coordinates.L1 S →L[ℝ]
      NoBorelUpperBoundFSigma.L1Coordinates.L1 S :=
  NoBorelUpperBoundFSigma.TreeOperators.operator (oldTree T)

theorem treeOperator_injective (T : WF) : Function.Injective (treeOperator T) := by
  apply NoBorelUpperBoundFSigma.TreeOperators.operator_injective_of_not_hasBranch (oldTree T)
  exact T.property

def tensorSubspace (T : WF) : Submodule ℝ Space :=
  NoBorelUpperBoundFSigma.SymmetricTensor.imageSubmodule (treeOperator T) []

def sourceRelation (T : WF) (x y : Space) : Prop := y-x ∈ tensorSubspace T

end ModNullUniversality.CompactTensor

end
end
-- END COMPLETE MODULE ModNullProof.TensorFamily

-- BEGIN COMPLETE MODULE ModNullProof.CompactCosets
section
                                    
                                   
                                

set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace

namespace ModNullUniversality.CompactTensor

def push (x : Space) : Target := Multiplicative.ofAdd (sourceEmbedding x)

theorem continuous_push : Continuous push := continuous_sourceEmbedding

theorem push_injective : Function.Injective push := sourceEmbedding_injective

def compactSubgroup (H : Submodule ℝ Space) : Subgroup Target :=
  H.toAddSubgroup.toSubgroup.map sourceEmbedding.toMultiplicative

theorem compactSubgroup_carrier (H : Submodule ℝ Space) :
    (compactSubgroup H : Set Target) = push '' (H : Set Space) := by
  ext y
  rfl

theorem coset_push_iff (H : Submodule ℝ Space) (x y : Space) :
    CosetRelation compactGroup (compactSubgroup H) (push x) (push y) ↔ y-x ∈ H := by
  change -sourceEmbedding x + sourceEmbedding y ∈
    (H.toAddSubgroup.map sourceEmbedding : Set AddTarget) ↔ y-x ∈ H
  rw [← sub_eq_neg_add,← map_sub]
  exact AddSubgroup.mem_map_iff_mem sourceEmbedding_injective

theorem source_reduces_compact (T : WF) :
    BorelReducible (sourceRelation T)
      (CosetRelation compactGroup (compactSubgroup (tensorSubspace T))) := by
  exact ⟨push,continuous_push.measurable,fun x y => (coset_push_iff _ x y).symm⟩

def ambientPush (x : Ambient) : Target := Multiplicative.ofAdd (embedding x)

theorem continuous_ambientPush : Continuous ambientPush := continuous_embedding

theorem ambientPush_injective : Function.Injective ambientPush := embedding_injective

theorem compactSubgroup_differenceFSigma (H : Submodule ℝ Space)
    (hH : ∃ A B : Set Ambient, IsKSigma A ∧ IsKSigma B ∧
      coordinates '' (H : Set Space) = A \ B) :
    DifferenceFSigma (compactSubgroup H : Set Target) := by
  obtain ⟨A,B,hA,hB,hEq⟩ := hH
  have heq : (compactSubgroup H : Set Target) = ambientPush '' (A \ B) := by
    rw [← hEq,compactSubgroup_carrier,image_image]
    rfl
  rw [heq]
  exact differenceFSigma_image_of_ksigma ambientPush continuous_ambientPush
    ambientPush_injective A B hA hB

theorem compactSubgroup_graph_differenceFSigma (H : Submodule ℝ Space)
    (hH : DifferenceFSigma (compactSubgroup H : Set Target)) :
    DifferenceFSigma {p : Target × Target |
      CosetRelation compactGroup (compactSubgroup H) p.1 p.2} := by
  exact differenceFSigma_preimage hH (fun p : Target × Target => p.1⁻¹ * p.2)
    (continuous_fst.inv.mul continuous_snd)

theorem compactSubgroup_lowComplexity (H : WF → Submodule ℝ Space)
    (hH : ∀ T, ∃ A B : Set Ambient, IsKSigma A ∧ IsKSigma B ∧
      coordinates '' (H T : Set Space) = A \ B) :
    LowComplexityFamily compactGroup (fun T => compactSubgroup (H T)) := by
  have hd (T : WF) := compactSubgroup_differenceFSigma (H T) (hH T)
  have hg (T : WF) := compactSubgroup_graph_differenceFSigma (H T) (hd T)
  exact ⟨fun T => differenceFSigma_isDelta3 (hd T),
    fun T => differenceFSigma_isDelta3 (hg T),hg⟩

end ModNullUniversality.CompactTensor

end
end
-- END COMPLETE MODULE ModNullProof.CompactCosets

-- BEGIN COMPLETE MODULE ModNullProof.LinearCosets
section
                               
                                     

set_option autoImplicit false
noncomputable section
open Set Topology

namespace ModNullUniversality.LinearCosets

open NoBorelUpperBoundFSigma
open NoBorelUpperBoundFSigma.L1Coordinates
open NoBorelUpperBoundFSigma.SymmetricTensor
open NoBorelUpperBoundFSigma.Construction

def residual (D : A →L[ℝ] A) (x : X) : A := x.2 - D x.1

def correction (D : A →L[ℝ] A) (g : G) : C :=
  (0, (1 / 2 : ℝ) • outer (residual D g.1) g.2.1.1)

def theta (D : A →L[ℝ] A) (g : G) : (A × A) × C :=
  ((residual D g.1, residual D g.2.1), g.2.2 - correction D g)

def TensorRelation (D : A →L[ℝ] A) (c d : C) : Prop :=
  d - c ∈ imageSubmodule D []

theorem continuous_residual (D : A →L[ℝ] A) : Continuous (residual D) :=
  continuous_snd.sub (D.continuous.comp continuous_fst)

theorem continuous_correction (D : A →L[ℝ] A) : Continuous (correction D) := by
  exact continuous_const.prodMk
    ((continuous_outer.comp (((continuous_residual D).comp continuous_fst).prodMk
      continuous_snd.fst.fst)).const_smul (1 / 2 : ℝ))

theorem continuous_theta (D : A →L[ℝ] A) : Continuous (theta D) :=
  (((continuous_residual D).comp continuous_fst).prodMk
    ((continuous_residual D).comp continuous_snd.fst)).prodMk
      (continuous_snd.snd.sub (continuous_correction D))

theorem mem_graph_iff (D : A →L[ℝ] A) (x : X) :
    x ∈ (graphMap D).range ↔ residual D x = 0 := by
  constructor
  · rintro ⟨a,rfl⟩
    simp [residual,graphMap_apply]
  · intro h
    exact ⟨x.1,Prod.ext rfl (sub_eq_zero.mp h).symm⟩

theorem residual_sub (D : A →L[ℝ] A) (x y : X) :
    residual D (y-x) = residual D y - residual D x := by
  change (y.2-x.2)-D (y.1-x.1) = (y.2-D y.1)-(x.2-D x.1)
  rw [map_sub]
  abel

theorem beta_residual (D : A →L[ℝ] A) (x : X) (e : A) :
    beta x (graphMap D e) =
      imageMap D [] (sym x.1 e) + (0, (1/2 : ℝ) • outer (residual D x) e) := by
  apply Prod.ext
  · change x.1 [] * e [] = (1/2 : ℝ) * (x.1 [] * e [] + e [] * x.1 []) + 0
    ring
  · change (1/2 : ℝ) • (outer x.2 e + outer (D e) x.1) =
      mapLeft D (sym x.1 e) + (1/2 : ℝ) • outer (residual D x) e
    rw [mapLeft_sym]
    ext ij
    change (1/2 : ℝ) * (x.2 ij.1 * e ij.2 + (D e) ij.1 * x.1 ij.2) =
      (1/2 : ℝ) * ((D x.1) ij.1 * e ij.2 + (D e) ij.1 * x.1 ij.2) +
        (1/2 : ℝ) * ((x.2 ij.1 - (D x.1) ij.1) * e ij.2)
    ring

theorem inv_mul_coordinates (g h : G) :
    g⁻¹ * h = (h.1-g.1,h.2.1-g.2.1,h.2.2-g.2.2-beta g.1 (h.2.1-g.2.1)) := by
  rw [CentralExtension.inv_def,CentralExtension.mul_def]
  apply Prod.ext
  · change -g.1+h.1 = h.1-g.1
    abel
  · apply Prod.ext
    · change -g.2.1+h.2.1 = h.2.1-g.2.1
      abel
    · simp only [map_neg,map_sub,ContinuousLinearMap.neg_apply]
      abel

theorem subgroup_mem_iff (D : A →L[ℝ] A) (g : G) :
    g ∈ subgroup D ↔
      residual D g.1 = 0 ∧ residual D g.2.1 = 0 ∧ g.2.2 ∈ imageSubmodule D [] := by
  rw [subgroup,CentralExtension.generatedAxes_eq_coordinateSubgroup]
  change g.1 ∈ (graphMap D).range ∧ g.2.1 ∈ (graphMap D).range ∧
      g.2.2 ∈ CentralExtension.centralSpan beta (graphMap D) ↔ _
  rw [centralSpan_eq_imageSubmodule,mem_graph_iff,mem_graph_iff]

theorem correction_sub (D : A →L[ℝ] A) (g h : G)
    (hr : residual D g.1 = residual D h.1) :
    correction D h - correction D g =
      (0, (1/2 : ℝ) • outer (residual D g.1) (h.2.1.1-g.2.1.1)) := by
  apply Prod.ext
  · simp [correction]
  · change (1/2 : ℝ) • outer (residual D h.1) h.2.1.1 -
      (1/2 : ℝ) • outer (residual D g.1) g.2.1.1 = _
    rw [← hr]
    ext ij
    change (1/2 : ℝ) * (residual D g.1 ij.1 * h.2.1.1 ij.2) -
      (1/2 : ℝ) * (residual D g.1 ij.1 * g.2.1.1 ij.2) =
        (1/2 : ℝ) * (residual D g.1 ij.1 * (h.2.1.1 ij.2-g.2.1.1 ij.2))
    ring

theorem graph_difference (D : A →L[ℝ] A) (x y : X)
    (h : residual D x = residual D y) :
    y-x = graphMap D (y.1-x.1) := by
  apply Prod.ext
  · rfl
  · change y.2-x.2 = D (y.1-x.1)
    rw [map_sub]
    have hh : x.2-D x.1 = y.2-D y.1 := h
    calc
      y.2-x.2 = (y.2-D y.1)-(x.2-D x.1)+(D y.1-D x.1) := by abel
      _ = D y.1-D x.1 := by rw [hh]; abel

theorem coset_iff_theta (D : A →L[ℝ] A) (g h : G) :
    GroupCosetRelation (subgroup D) g h ↔
      (theta D g).1 = (theta D h).1 ∧
        TensorRelation D (theta D g).2 (theta D h).2 := by
  rw [GroupCosetRelation,inv_mul_coordinates,subgroup_mem_iff]
  simp only [residual_sub,sub_eq_zero]
  change (residual D h.1 = residual D g.1 ∧
    residual D h.2.1 = residual D g.2.1 ∧
      h.2.2-g.2.2-beta g.1 (h.2.1-g.2.1) ∈ imageSubmodule D []) ↔ _
  by_cases hr : residual D g.1 = residual D h.1
  · by_cases hs : residual D g.2.1 = residual D h.2.1
    · have heq : (theta D g).1 = (theta D h).1 := Prod.ext hr hs
      simp only [hr.symm,hs.symm,true_and,heq]
      rw [graph_difference D g.2.1 h.2.1 hs,beta_residual]
      have hmem : imageMap D [] (sym g.1.1 (h.2.1.1-g.2.1.1)) ∈ imageSubmodule D [] :=
        ⟨_,sym_mem _ _,rfl⟩
      have hid :
          h.2.2-g.2.2-
              (imageMap D [] (sym g.1.1 (h.2.1.1-g.2.1.1)) +
                (0,(1/2 : ℝ) • outer (residual D g.1) (h.2.1.1-g.2.1.1))) =
            ((theta D h).2-(theta D g).2) -
              imageMap D [] (sym g.1.1 (h.2.1.1-g.2.1.1)) := by
        dsimp only [theta]
        rw [show h.2.2-correction D h-(g.2.2-correction D g) =
            h.2.2-g.2.2-(correction D h-correction D g) by abel]
        rw [correction_sub D g h hr]
        abel
      rw [hid]
      exact (imageSubmodule D []).sub_mem_iff_left hmem
    · constructor
      · rintro ⟨_,h,_⟩
        exact (hs h.symm).elim
      · rintro ⟨h,_⟩
        exact (hs (congrArg Prod.snd h)).elim
  · constructor
    · rintro ⟨h,_⟩
      exact (hr h.symm).elim
    · rintro ⟨h,_⟩
      exact (hr (congrArg Prod.fst h)).elim

end ModNullUniversality.LinearCosets

end
end
-- END COMPLETE MODULE ModNullProof.LinearCosets

-- BEGIN COMPLETE MODULE NoBorelUpperBound.UniversalAnalytic
section
                                  

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter TopologicalSpace Topology MeasureTheory

namespace NoBorelUpperBoundFSigma.Trees

def codeIndex (s t : Node) : ℕ := Encodable.encode (s, t)

/-- A universal projection of a closed relation, with a Baire-space code. -/
def Universal (c x : Baire) : Prop :=
  ∃ y : Baire, ∀ n, c (codeIndex (branchPrefix x n) (branchPrefix y n)) = 0

def graphCode (f : Baire → Baire) (k : ℕ) : ℕ :=
  match Encodable.decode (α := Node × Node) k with
  | none => 1
  | some (s, t) =>
    if ∃ a : Baire, branchPrefix (f a) s.length = s ∧ branchPrefix a t.length = t then 0 else 1

@[simp] theorem graphCode_index_eq_zero (f : Baire → Baire) (s t : Node) :
    graphCode f (codeIndex s t) = 0 ↔
      ∃ a : Baire, branchPrefix (f a) s.length = s ∧ branchPrefix a t.length = t := by
  simp [graphCode, codeIndex]

theorem tendsto_of_prefix_agreement (u : ℕ → Baire) (x : Baire)
    (h : ∀ n, branchPrefix (u n) n = branchPrefix x n) : Tendsto u atTop (𝓝 x) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have heq : ∀ᶠ n in atTop, u n i = x i := by
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    exact congrFun (List.ofFn_injective (h n)) ⟨i, by omega⟩
  exact tendsto_const_nhds.congr' (heq.mono fun _ h => h.symm)

theorem universal_graphCode_iff (f : Baire → Baire) (hf : Continuous f) (x : Baire) :
    Universal (graphCode f) x ↔ x ∈ range f := by
  constructor
  · rintro ⟨y, hy⟩
    have hex (n : ℕ) : ∃ a : Baire,
        branchPrefix (f a) n = branchPrefix x n ∧ branchPrefix a n = branchPrefix y n := by
      simpa only [graphCode_index_eq_zero, length_branchPrefix] using hy n
    choose a ha hb using hex
    have h₁ := tendsto_of_prefix_agreement a y hb
    have h₂ := tendsto_of_prefix_agreement (fun n => f (a n)) x ha
    exact ⟨y, tendsto_nhds_unique (hf.tendsto y |>.comp h₁) h₂⟩
  · rintro ⟨y, rfl⟩
    refine ⟨y, fun n => ?_⟩
    apply (graphCode_index_eq_zero _ _ _).mpr
    simpa only [length_branchPrefix] using (show ∃ a : Baire,
      branchPrefix (f a) n = branchPrefix (f y) n ∧ branchPrefix a n = branchPrefix y n from
        ⟨y, rfl, rfl⟩)

theorem exists_universal_code {s : Set Baire} (hs : AnalyticSet s) :
    ∃ c : Baire, ∀ x, Universal c x ↔ x ∈ s := by
  rw [AnalyticSet] at hs
  rcases hs with rfl | ⟨f, hf, heq⟩
  · refine ⟨fun _ => 1, fun x => ?_⟩
    constructor
    · rintro ⟨y, hy⟩
      have h := hy 0
      norm_num at h
    · exact False.elim
  · exact ⟨graphCode f, fun x => by rw [universal_graphCode_iff f hf x, heq]⟩

/-- The universal analytic relation cannot itself be Borel, by diagonalization. -/
theorem not_borel_universal :
    ¬ @MeasurableSet (Baire × Baire) (borel (Baire × Baire))
      {p | Universal p.1 p.2} := by
  letI : MeasurableSpace Baire := borel Baire
  letI : BorelSpace Baire := ⟨rfl⟩
  intro h
  have hu : MeasurableSet {p : Baire × Baire | Universal p.1 p.2} := by
    have heq : (inferInstance : MeasurableSpace (Baire × Baire)) = borel (Baire × Baire) :=
      BorelSpace.measurable_eq
    rwa [← heq] at h
  have hd : MeasurableSet {x : Baire | ¬ Universal x x} :=
    hu.compl.preimage ((continuous_id.prodMk continuous_id).measurable)
  obtain ⟨c, hc⟩ := exists_universal_code hd.analyticSet
  have hcc := hc c
  change Universal c c ↔ ¬ Universal c c at hcc
  exact iff_not_self hcc

end NoBorelUpperBoundFSigma.Trees

end
end
-- END COMPLETE MODULE NoBorelUpperBound.UniversalAnalytic

-- BEGIN COMPLETE MODULE NoBorelUpperBound.IllFoundedNonBorel
section
                                          

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter TopologicalSpace Topology MeasureTheory

namespace NoBorelUpperBoundFSigma.Trees

@[simp] theorem take_branchPrefix (x : Baire) (n k : ℕ) :
    (branchPrefix x n).take k = branchPrefix x (min k n) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [branchPrefix]

def codeTree (c x : Baire) : TreeSpace :=
  ⟨fun s => decide (∀ k : Fin (s.length + 1),
      c (codeIndex (branchPrefix x k) (s.take k)) = 0), by
    intro s a hs
    apply decide_eq_true
    intro k
    have hprop : ∀ k : Fin ((s ++ [a]).length + 1),
        c (codeIndex (branchPrefix x k) ((s ++ [a]).take k)) = 0 := of_decide_eq_true hs
    have hk : (k : ℕ) ≤ s.length := by omega
    have h := hprop ⟨k, by simpa using Nat.lt.step k.isLt⟩
    simpa only [List.take_append_of_le_length hk] using h⟩

theorem codeTree_mem_iff (c x : Baire) (s : Node) :
    codeTree c x s = true ↔ ∀ k : Fin (s.length + 1),
      c (codeIndex (branchPrefix x k) (s.take k)) = 0 := by
  simp only [codeTree, decide_eq_true_eq]

theorem codeTree_hasBranch_iff (c x : Baire) : HasBranch (codeTree c x) ↔ Universal c x := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, fun n => ?_⟩
    have h := (codeTree_mem_iff c x (branchPrefix y n)).mp (hy n)
      ⟨n, by simp⟩
    simpa using h
  · rintro ⟨y, hy⟩
    refine ⟨y, fun n => (codeTree_mem_iff c x (branchPrefix y n)).mpr ?_⟩
    intro k
    have hk : (k : ℕ) ≤ n := by
      have h := k.isLt
      simp only [length_branchPrefix] at h
      omega
    simpa only [take_branchPrefix, Nat.min_eq_left hk] using hy k

theorem continuous_variable_evaluation : Continuous (fun p : Baire × ℕ => p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have heq : ∀ᶠ q : Baire × ℕ in 𝓝 p, q.2 = p.2 :=
    (continuous_snd.tendsto p).eventually ((isOpen_discrete {p.2}).mem_nhds rfl)
  have h : ContinuousAt (fun q : Baire × ℕ => q.1 p.2) p :=
    ((continuous_apply p.2).comp continuous_fst).continuousAt
  apply h.congr_of_eventuallyEq
  filter_upwards [heq] with q hq
  rw [hq]

theorem continuous_codeTree : Continuous (fun p : Baire × Baire => codeTree p.1 p.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro s
  apply (continuous_bool_rng true).mpr
  have heq : (fun p : Baire × Baire => decide (∀ k : Fin (s.length + 1),
      p.1 (codeIndex (branchPrefix p.2 k) (s.take k)) = 0)) ⁻¹' {true} =
      ⋂ k : Fin (s.length + 1),
        {p : Baire × Baire | p.1 (codeIndex (branchPrefix p.2 k) (s.take k)) = 0} := by
    ext p
    simp
  rw [heq]
  apply isClopen_iInter_of_finite
  intro k
  apply (isClopen_discrete {(0 : ℕ)}).preimage
  have hindex : Continuous (fun p : Baire × Baire => codeIndex (branchPrefix p.2 k) (s.take k)) :=
    (continuous_of_discreteTopology : Continuous (fun s' : Node => codeIndex s' (s.take k))).comp
      ((continuous_branchPrefix k).comp continuous_snd)
  simpa only [Function.comp_def] using
    continuous_variable_evaluation.comp (continuous_fst.prodMk hindex)

/-- Ill-founded trees, with the compact topology on their membership bits,
form a non-Borel set. This proof includes the universal analytic diagonal. -/
theorem not_borel_IF : ¬ @MeasurableSet TreeSpace (borel TreeSpace) IF := by
  intro h
  apply not_borel_universal
  have hm : @Measurable (Baire × Baire) TreeSpace (borel (Baire × Baire)) (borel TreeSpace)
      (fun p => codeTree p.1 p.2) := continuous_codeTree.borel_measurable
  have hpre := hm h
  convert hpre using 1
  ext p
  exact (codeTree_hasBranch_iff p.1 p.2).symm

end NoBorelUpperBoundFSigma.Trees

end
end
-- END COMPLETE MODULE NoBorelUpperBound.IllFoundedNonBorel

-- BEGIN COMPLETE MODULE NoBorelUpperBound.ConstructionFamily
section
                                     
                                           

noncomputable section
set_option maxHeartbeats 800000
open Set Topology MeasureTheory

namespace NoBorelUpperBoundFSigma.Construction
open L1Coordinates SymmetricTensor TreeOperators Trees

abbrev Axis := Multiplicative A

instance : PolishSpace Axis := inferInstanceAs (PolishSpace A)

def graphHom (D : A →L[ℝ] A) : Axis →* Multiplicative X :=
  (graphMap D).toLinearMap.toAddMonoidHom.toMultiplicative

def family (n : ℕ) (T : TreeSpace) : Axis →* G :=
  if n = 0 then (CentralExtension.leftHom beta).comp (graphHom (operator T))
  else (CentralExtension.rightHom beta).comp (graphHom (operator T))

@[simp] theorem family_zero (T : TreeSpace) (a : Axis) :
    family 0 T a = CentralExtension.left beta (graphMap (operator T) a.toAdd) := by
  simp [family,graphHom,CentralExtension.leftHom]

theorem family_of_ne_zero {n : ℕ} (hn : n ≠ 0) (T : TreeSpace) (a : Axis) :
    family n T a = CentralExtension.right beta (graphMap (operator T) a.toAdd) := by
  simp [family,hn,graphHom,CentralExtension.rightHom]

theorem generatedSubgroup_family (T : TreeSpace) :
    GeneratedSubgroup family T = subgroup (operator T) := by
  apply congrArg Subgroup.closure
  ext g
  constructor
  · rintro ⟨_,⟨n,rfl⟩,a,rfl⟩
    by_cases hn : n = 0
    · subst n
      exact Or.inl ⟨a.toAdd,(family_zero T a).symm⟩
    · exact Or.inr ⟨a.toAdd,(family_of_ne_zero hn T a).symm⟩
  · rintro (⟨a,rfl⟩ | ⟨a,rfl⟩)
    · exact mem_iUnion.mpr ⟨0,⟨Multiplicative.ofAdd a,family_zero T _⟩⟩
    · exact mem_iUnion.mpr ⟨1,⟨Multiplicative.ofAdd a,family_of_ne_zero (by decide) T _⟩⟩

theorem continuous_graph_family : Continuous (fun p : TreeSpace × Axis =>
    graphMap (operator p.1) p.2.toAdd) := by
  change Continuous (fun p : TreeSpace × Axis =>
    (p.2.toAdd,operator p.1.val p.2.toAdd))
  have h1 : Continuous (fun p : TreeSpace × Axis => (p.1.val : Code)) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous (fun p : TreeSpace × Axis => p.2.toAdd) := continuous_snd
  have hp : Continuous (fun p : TreeSpace × Axis => (p.1.val,p.2.toAdd)) := h1.prodMk h2
  have ho := continuous_operator.comp hp
  exact h2.prodMk ho

theorem continuous_family (n : ℕ) :
    Continuous (fun p : TreeSpace × Axis => family n p.1 p.2) := by
  by_cases hn : n = 0
  · subst n
    simp only [family_zero]
    change Continuous (fun p : TreeSpace × Axis =>
      (graphMap (operator p.1) p.2.toAdd, (0 : X), (0 : C)))
    exact continuous_graph_family.prodMk (continuous_const.prodMk continuous_const)
  · simp only [family_of_ne_zero hn]
    change Continuous (fun p : TreeSpace × Axis =>
      ((0 : X), graphMap (operator p.1) p.2.toAdd, (0 : C)))
    exact continuous_const.prodMk (continuous_graph_family.prodMk continuous_const)

theorem continuous_family_fixed (n : ℕ) (T : TreeSpace) : Continuous (family n T) := by
  have hc : Continuous (fun a : Axis => (T,a)) := continuous_const.prodMk continuous_id
  have hf := (continuous_family n).comp hc
  exact hf

theorem membershipSet_family : MembershipSet family (fun _ => designated) = IF := by
  ext T
  change designated ∈ GeneratedSubgroup family T ↔ HasBranch T
  rw [generatedSubgroup_family,designated_mem_tree_iff]

end NoBorelUpperBoundFSigma.Construction

end
end
-- END COMPLETE MODULE NoBorelUpperBound.ConstructionFamily

-- BEGIN COMPLETE MODULE NoBorelUpperBound.CategoryProduct
section
                                             
                                    
                                                
                     

noncomputable section
open Set Filter TopologicalSpace Topology

namespace NoBorelUpperBoundFSigma
universe u v

section Product
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

def sectionHit (U : Set (X × Y)) (V : Set Y) : Set X :=
  Prod.fst '' (U ∩ (univ ×ˢ V))

theorem isOpen_sectionHit {U : Set (X × Y)} {V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V) : IsOpen (sectionHit U V) :=
  isOpenMap_fst _ (hU.inter (isOpen_univ.prod hV))

theorem dense_sectionHit {U : Set (X × Y)} {V : Set Y}
    (hU : Dense U) (hV : IsOpen V) (hne : V.Nonempty) : Dense (sectionHit U V) := by
  apply dense_iff_inter_open.mpr
  intro W hW hWne
  obtain ⟨p, hpWV, hpU⟩ := hU.inter_open_nonempty (W ×ˢ V) (hW.prod hV) (hWne.prod hne)
  exact ⟨p.1, hpWV.1, ⟨p, ⟨hpU, ⟨mem_univ _, hpWV.2⟩⟩, rfl⟩⟩

/-- The residual-section half of the Kuratowski--Ulam theorem. -/
theorem residual_sections [SecondCountableTopology Y] {s : Set (X × Y)}
    (hs : s ∈ residual (X × Y)) :
    ∀ᶠ x in residual X, {y | (x, y) ∈ s} ∈ residual Y := by
  classical
  obtain ⟨S, hSo, hSd, hSc, hSs⟩ := mem_residual_iff.mp hs
  letI : Countable S := hSc.to_subtype
  have hgood : ∀ᶠ x in residual X, ∀ U : S, ∀ V : countableBasis Y,
      x ∈ sectionHit U.val V.val := by
    apply eventually_countable_forall.mpr
    intro U
    apply eventually_countable_forall.mpr
    intro V
    exact residual_of_dense_open
      (isOpen_sectionHit (hSo U U.property) (isOpen_of_mem_countableBasis V.property))
      (dense_sectionHit (hSd U U.property) (isOpen_of_mem_countableBasis V.property)
        (nonempty_of_mem_countableBasis V.property))
  filter_upwards [hgood] with x hx
  have hsection (U : S) : {y | (x, y) ∈ U.val} ∈ residual Y := by
    apply residual_of_dense_open
    · exact (hSo U U.property).preimage (continuous_const.prodMk continuous_id)
    · apply (isBasis_countableBasis Y).dense_iff.mpr
      intro V hV _
      obtain ⟨⟨a,b⟩, ⟨hpU, hpV⟩, hpx⟩ := hx U ⟨V, hV⟩
      dsimp at hpx
      subst a
      exact ⟨b, hpV.2, hpU⟩
  have htotal : (⋂ U : S, {y | (x, y) ∈ U.val}) ∈ residual Y :=
    countable_iInter_mem.mpr hsection
  apply mem_of_superset htotal
  intro y hy
  apply hSs
  intro U hU
  exact mem_iInter.mp hy ⟨U, hU⟩

/-- A saturated residual set in a nonempty Baire product reflects to its
first factor. No regularity assumption on the saturated set is required. -/
theorem residual_of_preimage_fst [SecondCountableTopology Y] [BaireSpace Y] [Nonempty Y]
    {s : Set X} (hs : Prod.fst ⁻¹' s ∈ residual (X × Y)) : s ∈ residual X := by
  filter_upwards [residual_sections hs] with x hx
  obtain ⟨y, hy⟩ := (dense_of_mem_residual hx).nonempty
  exact hy

/-- The Kuratowski--Ulam equivalence for sets with the property of Baire. -/
theorem residual_product_iff [SecondCountableTopology Y] [BaireSpace X] [BaireSpace Y]
    {s : Set (X × Y)} (hs : BaireMeasurableSet s) :
    s ∈ residual (X × Y) ↔ ∀ᶠ x in residual X, {y | (x,y) ∈ s} ∈ residual Y := by
  refine ⟨residual_sections, ?_⟩
  intro hsec
  obtain ⟨U, hU, heq⟩ := hs.residualEq_isOpen
  have heqp : ∀ᶠ p in residual (X × Y), p ∈ s ↔ p ∈ U := eventuallyEq_set.mp heq
  have hUsec : ∀ᶠ x in residual X, {y | (x,y) ∈ U} ∈ residual Y := by
    filter_upwards [hsec, residual_sections heqp] with x hx hxEq
    filter_upwards [hx, hxEq] with y hy hEq
    exact hEq.mp hy
  have hUd : Dense U := by
    apply dense_iff_inter_open.mpr
    intro W hW hWne
    obtain ⟨⟨x,y⟩, hxy⟩ := hWne
    obtain ⟨A,B,hA,hB,hx,hy,hAB⟩ := isOpen_prod_iff.mp hW x y hxy
    obtain ⟨a,ha,haSec⟩ := (dense_of_mem_residual hUsec).inter_open_nonempty A hA ⟨x,hx⟩
    obtain ⟨b,hb,hab⟩ := (dense_of_mem_residual haSec).inter_open_nonempty B hB ⟨y,hy⟩
    exact ⟨(a,b), hAB ⟨ha,hb⟩, hab⟩
  filter_upwards [residual_of_dense_open hU hUd, heqp] with p hp hEq
  exact hEq.mpr hp

end Product
end NoBorelUpperBoundFSigma

end
end
-- END COMPLETE MODULE NoBorelUpperBound.CategoryProduct

-- BEGIN COMPLETE MODULE NoBorelUpperBound.CategoryTransfer
section
                                                        
                                        
                     

noncomputable section
open Set Filter TopologicalSpace Topology MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v w z

section Collapse
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Y : Type v} (f : G → Y) (F : Setoid Y)

/-- Translation by `t` generically preserves the target equivalence class. -/
def GenericallyCollapses (t : G) : Prop :=
  ∀ᶠ g in residual G, F.r (f g) (f (g * t))

/-- The translations generically collapsed by any map form a subgroup. -/
def collapseSubgroup : Subgroup G where
  carrier := {t | GenericallyCollapses f F t}
  one_mem' := by
    change ∀ᶠ g in residual G, F.r (f g) (f (g*1))
    apply Eventually.of_forall
    intro g
    simpa only [mul_one] using F.refl (f g)
  mul_mem' := by
    intro a b ha hb
    change ∀ᶠ g in residual G, F.r (f g) (f (g*a)) at ha
    change ∀ᶠ g in residual G, F.r (f g) (f (g*b)) at hb
    change ∀ᶠ g in residual G, F.r (f g) (f (g*(a*b)))
    have hb' := tendsto_residual_of_isOpenMap (Homeomorph.mulRight a).continuous
      (Homeomorph.mulRight a).isOpenMap hb
    filter_upwards [ha, hb'] with g hga hgb
    simpa only [mul_assoc] using (F.trans hga hgb : F.r (f g) (f ((g*a)*b)))
  inv_mem' := by
    intro a ha
    change ∀ᶠ g in residual G, F.r (f g) (f (g*a)) at ha
    change ∀ᶠ g in residual G, F.r (f g) (f (g*a⁻¹))
    have ha' := tendsto_residual_of_isOpenMap (Homeomorph.mulRight a⁻¹).continuous
      (Homeomorph.mulRight a⁻¹).isOpenMap ha
    filter_upwards [ha'] with g hg
    apply F.symm
    change F.r (f (g*a⁻¹)) (f ((g*a⁻¹)*a)) at hg
    simpa only [inv_mul_cancel_right] using hg

@[simp] theorem mem_collapseSubgroup (t : G) :
    t ∈ collapseSubgroup f F ↔ GenericallyCollapses f F t := Iff.rfl

/-- A generic homomorphism test collapses every fixed image element. -/
theorem generic_homomorphism_fixed
    {A : Type w} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [SecondCountableTopology A] [BaireSpace A]
    (h : A →* G)
    (hgen : ∀ᶠ p : G × A in residual (G × A), F.r (f p.1) (f (p.1 * h p.2)))
    (a₀ : A) : GenericallyCollapses f F (h a₀) := by
  let e : G × A ≃ₜ G × A :=
    (Homeomorph.mulRight (h a₀)).prodCongr (Homeomorph.mulLeft a₀⁻¹)
  have hgen' := tendsto_residual_of_isOpenMap e.continuous e.isOpenMap hgen
  have hs : Prod.fst ⁻¹' {g | F.r (f g) (f (g * h a₀))} ∈ residual (G × A) := by
    filter_upwards [hgen,hgen'] with p hp hp'
    change F.r (f (p.1 * h a₀)) (f ((p.1 * h a₀) * h (a₀⁻¹*p.2))) at hp'
    have he : (p.1 * h a₀) * h (a₀⁻¹*p.2) = p.1 * h p.2 := by
      rw [map_mul,map_inv]
      group
    rw [he] at hp'
    exact F.trans hp (F.symm hp')
  exact residual_of_preimage_fst hs

/-- Simultaneous generic tests collapse the algebraic subgroup generated by
all homomorphism images. -/
theorem generated_subgroup_collapses
    {P : Type w} {A : ℕ → Type z} [∀ n, Group (A n)]
    [∀ n, TopologicalSpace (A n)] [∀ n, IsTopologicalGroup (A n)]
    [∀ n, SecondCountableTopology (A n)] [∀ n, BaireSpace (A n)]
    (h : ∀ n, P → (A n →* G)) (p : P)
    (hgen : ∀ n, ∀ᶠ ga : G × A n in residual (G × A n),
      F.r (f ga.1) (f (ga.1 * h n p ga.2))) :
    GeneratedSubgroup h p ≤ collapseSubgroup f F := by
  change Subgroup.closure _ ≤ _
  apply (Subgroup.closure_le _).2
  intro t ht
  obtain ⟨n, ht⟩ := mem_iUnion.mp ht
  obtain ⟨a, rfl⟩ := ht
  exact generic_homomorphism_fixed f F (h n p) (hgen n) a

/-- The generator tests and a generic separation test cannot coexist when
the designated element is in the algebraically generated subgroup. -/
theorem generic_tests_exclude_membership [BaireSpace G]
    {P : Type w} {A : ℕ → Type z} [∀ n, Group (A n)]
    [∀ n, TopologicalSpace (A n)] [∀ n, IsTopologicalGroup (A n)]
    [∀ n, SecondCountableTopology (A n)] [∀ n, BaireSpace (A n)]
    (h : ∀ n, P → (A n →* G)) (p : P) (t : G)
    (hgen : ∀ n, ∀ᶠ ga : G × A n in residual (G × A n),
      F.r (f ga.1) (f (ga.1 * h n p ga.2)))
    (hsep : ∀ᶠ g in residual G, ¬ F.r (f g) (f (g*t))) :
    t ∉ GeneratedSubgroup h p := by
  intro ht
  have hcollapse := generated_subgroup_collapses f F h p hgen ht
  have hfalse : ∀ᶠ g in residual G, False := by
    filter_upwards [hcollapse,hsep] with g hc hs
    exact hs hc
  obtain ⟨g,hg⟩ := (dense_of_mem_residual hfalse).nonempty
  exact hg

end Collapse

section Agreement
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type w} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    {Y : Type v}

/-- Triangular change of variables for right multiplication by a varying
continuous homomorphism value. -/
def homomorphismRightShear (h : A →* G) (hh : Continuous h) : G × A ≃ₜ G × A where
  toFun p := (p.1 * h p.2, p.2)
  invFun p := (p.1 * (h p.2)⁻¹, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := (continuous_fst.mul (hh.comp continuous_snd)).prodMk continuous_snd
  continuous_invFun := (continuous_fst.mul (hh.comp continuous_snd).inv).prodMk continuous_snd

theorem isOpenMap_mul_homomorphism (h : A →* G) (hh : Continuous h) :
    IsOpenMap (fun p : G × A => p.1 * h p.2) :=
  isOpenMap_fst.comp (homomorphismRightShear h hh).isOpenMap

/-- A map agreeing generically with an exact reduction passes the joint
generic homomorphism test. No measurable choice or category Fubini converse
is needed: both agreement sets are pulled back by continuous open maps. -/
theorem generic_test_of_reduction_agreement
    (f q : G → Y) (F : Setoid Y) (H : Subgroup G)
    (hred : ∀ g g', GroupCosetRelation H g g' ↔ F.r (f g) (f g'))
    (hag : ∀ᶠ g in residual G, q g = f g)
    (h : A →* G) (hh : Continuous h) (hH : ∀ a, h a ∈ H) :
    ∀ᶠ p : G × A in residual (G × A), F.r (q p.1) (q (p.1 * h p.2)) := by
  have hag₁ := tendsto_residual_of_isOpenMap
    (continuous_fst : Continuous (Prod.fst : G × A → G)) isOpenMap_fst hag
  have hag₂ := tendsto_residual_of_isOpenMap
    (continuous_fst.mul (hh.comp continuous_snd)) (isOpenMap_mul_homomorphism h hh) hag
  filter_upwards [hag₁,hag₂] with p hp₁ hp₂
  change q p.1 = f p.1 at hp₁
  change q (p.1 * h p.2) = f (p.1 * h p.2) at hp₂
  rw [hp₁,hp₂]
  apply (hred _ _).mp
  simpa only [GroupCosetRelation, inv_mul_cancel_left] using hH p.2

theorem generic_separation_of_reduction_agreement
    (f q : G → Y) (F : Setoid Y) (H : Subgroup G)
    (hred : ∀ g g', GroupCosetRelation H g g' ↔ F.r (f g) (f g'))
    (hag : ∀ᶠ g in residual G, q g = f g) (t : G) (ht : t ∉ H) :
    ∀ᶠ g in residual G, ¬ F.r (q g) (q (g*t)) := by
  have hag₂ := tendsto_residual_of_isOpenMap (Homeomorph.mulRight t).continuous
    (Homeomorph.mulRight t).isOpenMap hag
  filter_upwards [hag,hag₂] with g hg hg₂
  change q (g*t) = f (g*t) at hg₂
  rw [hg,hg₂]
  intro heq
  have hm := (hred g (g*t)).mpr heq
  exact ht (by simpa only [GroupCosetRelation, inv_mul_cancel_left] using hm)

end Agreement
end NoBorelUpperBoundFSigma

end
end
-- END COMPLETE MODULE NoBorelUpperBound.CategoryTransfer

-- BEGIN COMPLETE MODULE NoBorelUpperBound.CategoryQuantifier
section
                                        
                                                       

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v

section LocalCategory
variable {X : Type u} [TopologicalSpace X] [SecondCountableTopology X] [BaireSpace X]

/-- The local category test for a Baire-measurable set can be witnessed on a
member of a fixed countable basis. -/
theorem nonmeagre_inter_iff_basic_meagre_compl {s U : Set X}
    (hs : BaireMeasurableSet s) (hU : IsOpen U) :
    ¬ IsMeagre (U ∩ s) ↔ ∃ V : countableBasis X,
      (V : Set X) ⊆ U ∧ IsMeagre ((V : Set X) ∩ sᶜ) := by
  classical
  constructor
  · intro hnon
    obtain ⟨O,hO,heq⟩ := hs.residualEq_isOpen
    have hdiff : IsMeagre {x | ¬ (x ∈ s ↔ x ∈ O)} := by
      change ∀ᶠ x in residual X, ¬¬(x ∈ s ↔ x ∈ O)
      exact (eventuallyEq_set.mp heq).mono (fun _ hx => not_not.mpr hx)
    have hUO : (U ∩ O).Nonempty := by
      by_contra hn
      apply hnon
      apply hdiff.mono
      intro x hx
      intro he
      exact hn ⟨x,hx.1,he.mp hx.2⟩
    obtain ⟨V,hV,hVne,hVsub⟩ :=
      (isBasis_countableBasis X).exists_nonempty_subset hUO (hU.inter hO)
    refine ⟨⟨V,hV⟩, (fun x hx => (hVsub hx).1), hdiff.mono ?_⟩
    intro x hx he
    exact hx.2 (he.mpr (hVsub hx.1).2)
  · rintro ⟨V,hVU,hVm⟩ hUm
    have hVmeagre : IsMeagre (V : Set X) := by
      have hVs : IsMeagre ((V : Set X) ∩ s) :=
        hUm.mono (inter_subset_inter_left _ hVU)
      have hu := hVs.union hVm
      exact hu.mono (by intro x hx; by_cases hxs : x ∈ s <;> simp_all)
    exact not_isMeagre_of_isOpen (isOpen_of_mem_countableBasis V.property)
      (nonempty_of_mem_countableBasis V.property) hVmeagre

end LocalCategory

section BorelQuantifier
variable {P : Type u} {X : Type v}
    [TopologicalSpace P] [PolishSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Nonmeagreness of a Borel section inside a fixed open set is a Borel
condition on the parameter. This is the Borel category quantifier. -/
theorem measurableSet_nonmeagre_sections {S : Set (P × X)} (hS : MeasurableSet S) :
    ∀ U : Set X, IsOpen U → MeasurableSet {p | ¬ IsMeagre (U ∩ {x | (p,x) ∈ S})} := by
  classical
  induction S,hS using MeasurableSet.induction_on_open with
  | isOpen S hS =>
    intro U hU
    have heq : {p | ¬ IsMeagre (U ∩ {x | (p,x) ∈ S})} = sectionHit S U := by
      ext p
      have hsec : IsOpen (U ∩ {x | (p,x) ∈ S}) :=
        hU.inter (hS.preimage (continuous_const.prodMk continuous_id))
      constructor
      · intro hn
        obtain ⟨x,hxU,hxS⟩ := nonempty_of_not_isMeagre hn
        exact ⟨(p,x),⟨hxS,mem_univ _,hxU⟩,rfl⟩
      · rintro ⟨⟨q,x⟩,⟨hxS,_,hxU⟩,hqp⟩
        dsimp at hqp
        subst q
        exact not_isMeagre_of_isOpen hsec ⟨x,hxU,hxS⟩
    rw [heq]
    exact (isOpen_sectionHit hS hU).measurableSet
  | compl S hS IH =>
    intro U hU
    have hsec (p : P) : BaireMeasurableSet {x | (p,x) ∈ Sᶜ} :=
      (hS.compl.preimage measurable_prodMk_left).baireMeasurableSet
    have heq : {p | ¬ IsMeagre (U ∩ {x | (p,x) ∈ Sᶜ})} =
        ⋃ V : countableBasis X, if (V : Set X) ⊆ U then
          {p | IsMeagre ((V : Set X) ∩ {x | (p,x) ∈ S})} else ∅ := by
      ext p
      simp only [mem_setOf_eq, mem_iUnion]
      rw [nonmeagre_inter_iff_basic_meagre_compl (hsec p) hU]
      constructor
      · rintro ⟨V,hVU,hVm⟩
        exact ⟨V, by simpa only [if_pos hVU, mem_setOf_eq, mem_compl_iff,
          Set.compl_setOf, not_not] using hVm⟩
      · rintro ⟨V,hVp⟩
        by_cases hVU : (V : Set X) ⊆ U
        · exact ⟨V,hVU,by simpa only [if_pos hVU, mem_setOf_eq, mem_compl_iff,
            Set.compl_setOf, not_not] using hVp⟩
        · simp only [if_neg hVU, mem_empty_iff_false] at hVp
    rw [heq]
    apply MeasurableSet.iUnion
    intro V
    split_ifs
    · simpa only [Set.compl_setOf, not_not] using
        (IH V (isOpen_of_mem_countableBasis V.property)).compl
    · exact MeasurableSet.empty
  | iUnion f _ hf IH =>
    intro U hU
    have heq : {p | ¬ IsMeagre (U ∩ {x | (p,x) ∈ ⋃ n, f n})} =
        ⋃ n, {p | ¬ IsMeagre (U ∩ {x | (p,x) ∈ f n})} := by
      ext p
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · intro hn
        by_contra he
        push Not at he
        apply hn
        have hi : IsMeagre (⋃ n, U ∩ {x | (p,x) ∈ f n}) := isMeagre_iUnion he
        convert hi using 1
        ext x
        simp only [mem_inter_iff, mem_setOf_eq, mem_iUnion]
        tauto
      · rintro ⟨n,hn⟩ hm
        apply hn
        exact hm.mono (by intro x hx; exact ⟨hx.1,⟨n,hx.2⟩⟩)
    rw [heq]
    exact MeasurableSet.iUnion (fun n => IH n U hU)

/-- Comeagreness of Borel sections is a Borel parameter condition. -/
theorem measurableSet_residual_sections {S : Set (P × X)} (hS : MeasurableSet S) :
    MeasurableSet {p | {x | (p,x) ∈ S} ∈ residual X} := by
  have h := (measurableSet_nonmeagre_sections hS.compl Set.univ isOpen_univ).compl
  convert h using 1
  ext p
  simp only [mem_setOf_eq, mem_compl_iff, not_not, Set.univ_inter, IsMeagre,
    Set.compl_setOf, not_not]

end BorelQuantifier
end NoBorelUpperBoundFSigma

end
end
-- END COMPLETE MODULE NoBorelUpperBound.CategoryQuantifier

-- BEGIN COMPLETE MODULE NoBorelUpperBound.CategoryMembership
section
                                                        
                                                       
                                             
                                                    

noncomputable section
open Set MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v w

namespace FiniteGeneratorWord

/-- A finite sequence of parameters, with the generator index fixed in advance. -/
def Domain (A : ℕ → Type w) : List ℕ → Type w
  | [] => PUnit
  | n :: l => A n × Domain A l

instance domainMeasurableSpace {A : ℕ → Type w} [∀ n, MeasurableSpace (A n)] :
    (l : List ℕ) → MeasurableSpace (Domain A l)
  | [] => inferInstanceAs (MeasurableSpace PUnit)
  | n :: l => @Prod.instMeasurableSpace (A n) (Domain A l) inferInstance
      (domainMeasurableSpace l)

instance domainStandardBorelSpace {A : ℕ → Type w} [∀ n, MeasurableSpace (A n)]
    [∀ n, StandardBorelSpace (A n)] : (l : List ℕ) → StandardBorelSpace (Domain A l)
  | [] => inferInstanceAs (StandardBorelSpace PUnit)
  | n :: l => by
      letI := domainStandardBorelSpace (A := A) l
      exact inferInstanceAs (StandardBorelSpace (A n × Domain A l))

def value {P : Type u} {G : Type v} [Group G] {A : ℕ → Type w}
    [∀ n, Group (A n)] (h : ∀ n, P → (A n →* G)) :
    (l : List ℕ) → P → Domain A l → G
  | [], _, _ => 1
  | n :: l, p, a => h n p a.1 * value h l p a.2

theorem measurable_value {P : Type u} [MeasurableSpace P]
    {G : Type v} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    {A : ℕ → Type w} [∀ n, Group (A n)] [∀ n, MeasurableSpace (A n)]
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2)) :
    ∀ l : List ℕ, Measurable (fun pa : P × Domain A l => value h l pa.1 pa.2) := by
  intro l
  induction l with
  | nil => exact measurable_const
  | cons n l IH =>
      exact ((hh n).comp (measurable_fst.prodMk measurable_snd.fst)).mul
        (IH.comp (measurable_fst.prodMk measurable_snd.snd))

theorem value_mem {P : Type u} {G : Type v} [Group G] {A : ℕ → Type w}
    [∀ n, Group (A n)] (h : ∀ n, P → (A n →* G)) (p : P) :
    ∀ (l : List ℕ) (a : Domain A l), value h l p a ∈ GeneratedSubgroup h p := by
  intro l
  induction l with
  | nil => intro a; exact (GeneratedSubgroup h p).one_mem
  | cons n l IH =>
      intro a
      exact (GeneratedSubgroup h p).mul_mem
        (Subgroup.subset_closure (mem_iUnion.mpr ⟨n,mem_range_self a.1⟩)) (IH a.2)

theorem list_representation {P : Type u} {G : Type v} [Group G] {A : ℕ → Type w}
    [∀ n, Group (A n)] (h : ∀ n, P → (A n →* G)) (p : P)
    (L : List (Σ n, A n)) :
    ∃ (l : List ℕ) (a : Domain A l),
      value h l p a = (L.map (fun x => h x.1 p x.2)).prod := by
  induction L with
  | nil => exact ⟨[],PUnit.unit,rfl⟩
  | cons x L IH =>
      obtain ⟨l,a,ha⟩ := IH
      exact ⟨x.1 :: l,(x.2,a),by simpa only [value,List.map_cons,List.prod_cons,ha]⟩

def listSubgroup {P : Type u} {G : Type v} [Group G] {A : ℕ → Type w}
    [∀ n, Group (A n)] (h : ∀ n, P → (A n →* G)) (p : P) : Subgroup G where
  carrier := {g | ∃ L : List (Σ n, A n), (L.map (fun x => h x.1 p x.2)).prod = g}
  one_mem' := ⟨[],rfl⟩
  mul_mem' := by
    rintro x y ⟨L,rfl⟩ ⟨M,rfl⟩
    exact ⟨L ++ M,by simp⟩
  inv_mem' := by
    rintro x ⟨L,rfl⟩
    refine ⟨(L.map (fun x => (⟨x.1,x.2⁻¹⟩ : Σ n, A n))).reverse,?_⟩
    simp only [List.map_reverse,List.map_map,Function.comp_def,map_inv]
    simpa only [List.map_map,Function.comp_def] using
      (List.prod_inv_reverse (L.map (fun x => h x.1 p x.2))).symm

theorem mem_iff_exists_value {P : Type u} {G : Type v} [Group G] {A : ℕ → Type w}
    [∀ n, Group (A n)] (h : ∀ n, P → (A n →* G)) (p : P) (g : G) :
    g ∈ GeneratedSubgroup h p ↔ ∃ (l : List ℕ) (a : Domain A l), value h l p a = g := by
  constructor
  · intro hg
    have hle : GeneratedSubgroup h p ≤ listSubgroup h p := by
      apply (Subgroup.closure_le _).2
      intro x hx
      obtain ⟨n,a,rfl⟩ := mem_iUnion.mp hx
      exact ⟨[⟨n,a⟩],by simp⟩
    obtain ⟨L,hL⟩ := hle hg
    obtain ⟨l,a,ha⟩ := list_representation h p L
    exact ⟨l,a,ha.trans hL⟩
  · rintro ⟨l,a,rfl⟩
    exact value_mem h p l a

end FiniteGeneratorWord

/-- Membership in an algebraically generated countable Borel family of
continuous-homomorphism images is analytic. Algebraic membership uses finite
words, with no topological closure involved. -/
theorem analyticSet_membershipSet
    {P : Type u} [TopologicalSpace P] [PolishSpace P] [MeasurableSpace P] [BorelSpace P]
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]
    {A : ℕ → Type w} [∀ n, Group (A n)] [∀ n, MeasurableSpace (A n)]
    [∀ n, StandardBorelSpace (A n)]
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2))
    (z₀ : P → G) (hz : Measurable z₀) : AnalyticSet (MembershipSet h z₀) := by
  classical
  have heq : MembershipSet h z₀ = ⋃ l : List ℕ,
      Prod.fst '' {pa : P × FiniteGeneratorWord.Domain A l |
        FiniteGeneratorWord.value h l pa.1 pa.2 = z₀ pa.1} := by
    ext p
    simp only [MembershipSet,mem_setOf_eq,mem_iUnion,mem_image,Prod.exists]
    rw [FiniteGeneratorWord.mem_iff_exists_value]
    constructor
    · rintro ⟨l,a,ha⟩
      exact ⟨l,p,a,ha,rfl⟩
    · rintro ⟨l,q,a,ha,rfl⟩
      exact ⟨l,a,ha⟩
  rw [heq]
  apply AnalyticSet.iUnion
  intro l
  have hS : MeasurableSet {pa : P × FiniteGeneratorWord.Domain A l |
      FiniteGeneratorWord.value h l pa.1 pa.2 = z₀ pa.1} :=
    measurableSet_eq_fun (FiniteGeneratorWord.measurable_value h hh l) (hz.comp measurable_fst)
  exact hS.analyticSet_image measurable_fst

end NoBorelUpperBoundFSigma

end
end
-- END COMPLETE MODULE NoBorelUpperBound.CategoryMembership

-- BEGIN COMPLETE MODULE NoBorelUpperBound.CategoryAnalytic
section
                                         
                                           
                                           
                                             

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v w z t

section Witness
variable {P : Type u} {C : Type v} {G : Type w} {A : ℕ → Type z} {Y : Type t}
    [Group G] [TopologicalSpace G]
    [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)]

/-- Generic generator invariance and generic designated-element separation. -/
def GenericWitness (h : ∀ n, P → (A n →* G)) (z₀ : P → G)
    (eval : C → G → Y) (F : Setoid Y) (pc : P × C) : Prop :=
  (∀ n, ∀ᶠ ga : G × A n in residual (G × A n),
    F.r (eval pc.2 ga.1) (eval pc.2 (ga.1 * h n pc.1 ga.2))) ∧
  (∀ᶠ g in residual G, ¬ F.r (eval pc.2 g) (eval pc.2 (g*z₀ pc.1)))

end Witness

section BorelWitness
variable {P : Type u} [TopologicalSpace P] [PolishSpace P]
    [MeasurableSpace P] [BorelSpace P]
    {C : Type v} [TopologicalSpace C] [PolishSpace C]
    [MeasurableSpace C] [BorelSpace C]
    {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]
    {A : ℕ → Type z} [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)]
    [∀ n, IsTopologicalGroup (A n)] [∀ n, PolishSpace (A n)]
    [∀ n, MeasurableSpace (A n)] [∀ n, BorelSpace (A n)]
    {Y : Type t} [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]

/-- The set of generic tests is genuinely Borel, including its category
quantifiers. -/
theorem measurableSet_genericWitness
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2))
    (z₀ : P → G) (hz : Measurable z₀)
    (eval : C → G → Y) (heval : Measurable (fun cg : C × G => eval cg.1 cg.2))
    (F : Setoid Y) (hF : IsBorelRelation F.r) :
    MeasurableSet {pc | GenericWitness h z₀ eval F pc} := by
  have hFb : MeasurableSet {yy : Y × Y | F.r yy.1 yy.2} := by
    unfold IsBorelRelation at hF
    rwa [← BorelSpace.measurable_eq] at hF
  have hgen (n : ℕ) : MeasurableSet {pc : P × C |
      ∀ᶠ ga : G × A n in residual (G × A n),
        F.r (eval pc.2 ga.1) (eval pc.2 (ga.1 * h n pc.1 ga.2))} := by
    apply measurableSet_residual_sections (S := {p : (P × C) × (G × A n) |
      F.r (eval p.1.2 p.2.1) (eval p.1.2 (p.2.1 * h n p.1.1 p.2.2))})
    apply hFb.preimage (f := fun p : (P × C) × (G × A n) =>
      (eval p.1.2 p.2.1, eval p.1.2 (p.2.1 * h n p.1.1 p.2.2)))
    apply Measurable.prodMk
    · exact heval.comp (measurable_fst.snd.prodMk measurable_snd.fst)
    · exact heval.comp (measurable_fst.snd.prodMk
        (measurable_snd.fst.mul ((hh n).comp
          (measurable_fst.fst.prodMk measurable_snd.snd))))
  have hsep : MeasurableSet {pc : P × C | ∀ᶠ g in residual G,
      ¬ F.r (eval pc.2 g) (eval pc.2 (g*z₀ pc.1))} := by
    apply measurableSet_residual_sections (S := {p : (P × C) × G |
      ¬ F.r (eval p.1.2 p.2) (eval p.1.2 (p.2 * z₀ p.1.1))})
    apply hFb.compl.preimage (f := fun p : (P × C) × G =>
      (eval p.1.2 p.2, eval p.1.2 (p.2 * z₀ p.1.1)))
    apply Measurable.prodMk
    · exact heval.comp (measurable_fst.snd.prodMk measurable_snd)
    · exact heval.comp (measurable_fst.snd.prodMk
        (measurable_snd.mul (hz.comp measurable_fst.fst)))
  have hforall : MeasurableSet {pc : P × C | ∀ n,
      ∀ᶠ ga : G × A n in residual (G × A n),
        F.r (eval pc.2 ga.1) (eval pc.2 (ga.1 * h n pc.1 ga.2))} := by
    simpa only [setOf_forall] using MeasurableSet.iInter hgen
  exact hforall.inter hsep

/-- Analytic generic witness projection equals the complement of membership
when actual reductions are available there. -/
theorem genericWitness_projection_eq_compl
    (h : ∀ n, P → (A n →* G)) (hc : ∀ n p, Continuous (h n p))
    (z₀ : P → G) (eval : C → G → Y) (F : Setoid Y)
    (hrep : ∀ f : G → Y, NoUniversalFSigma.IsBorelMeasurable f →
      ∃ c, ∀ᶠ g in residual G, eval c g = f g)
    (hbound : ∀ p, p ∉ MembershipSet h z₀ →
      BorelReducible (GroupCosetRelation (GeneratedSubgroup h p)) F.r) :
    Prod.fst '' {pc : P × C | GenericWitness h z₀ eval F pc} = (MembershipSet h z₀)ᶜ := by
  ext p
  constructor
  · rintro ⟨⟨q,c⟩,⟨hgen,hsep⟩,hqp⟩
    dsimp at hqp
    subst q
    exact generic_tests_exclude_membership (eval c) F h p (z₀ p) hgen hsep
  · intro hp
    obtain ⟨f,hf,hred⟩ := hbound p hp
    obtain ⟨c,hag⟩ := hrep f hf
    refine ⟨(p,c),⟨?_,?_⟩,rfl⟩
    · intro n
      exact generic_test_of_reduction_agreement f (eval c) F (GeneratedSubgroup h p)
        hred hag (h n p) (hc n p) (fun a => Subgroup.subset_closure (mem_iUnion.mpr ⟨n,mem_range_self a⟩))
    · exact generic_separation_of_reduction_agreement f (eval c) F (GeneratedSubgroup h p)
        hred hag (z₀ p) hp

/-- Category transfer once a universal Borel evaluation modulo meager
agreement and analyticity of the designated membership family are supplied.
Both premises are explicit infrastructure obligations. -/
theorem membership_measurable_of_generic_codes
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2))
    (hc : ∀ n p, Continuous (h n p))
    (z₀ : P → G) (hz : Measurable z₀)
    (eval : C → G → Y) (heval : Measurable (fun cg : C × G => eval cg.1 cg.2))
    (hrep : ∀ f : G → Y, NoUniversalFSigma.IsBorelMeasurable f →
      ∃ c, ∀ᶠ g in residual G, eval c g = f g)
    (F : Setoid Y) (hF : IsBorelRelation F.r)
    (hM : AnalyticSet (MembershipSet h z₀))
    (hbound : ∀ p, p ∉ MembershipSet h z₀ →
      BorelReducible (GroupCosetRelation (GeneratedSubgroup h p)) F.r) :
    MeasurableSet (MembershipSet h z₀) := by
  have hW := measurableSet_genericWitness h hh z₀ hz eval heval F hF
  have hproj : AnalyticSet (Prod.fst '' {pc : P × C | GenericWitness h z₀ eval F pc}) :=
    hW.analyticSet.image_of_continuous continuous_fst
  rw [genericWitness_projection_eq_compl h hc z₀ eval F hrep hbound] at hproj
  exact hM.measurableSet_of_compl hproj

/-- The generic homomorphism category-transfer principle. The sole coding
input is a jointly Borel family representing all Borel maps modulo meager
agreement. -/
theorem category_transfer_of_generic_codes
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2))
    (hc : ∀ n p, Continuous (h n p))
    (z₀ : P → G) (hz : Measurable z₀)
    (eval : C → G → Y) (heval : Measurable (fun cg : C × G => eval cg.1 cg.2))
    (hrep : ∀ f : G → Y, NoUniversalFSigma.IsBorelMeasurable f →
      ∃ c, ∀ᶠ g in residual G, eval c g = f g)
    (F : Setoid Y) (hF : IsBorelRelation F.r)
    (hbound : ∀ p, p ∉ MembershipSet h z₀ →
      BorelReducible (GroupCosetRelation (GeneratedSubgroup h p)) F.r) :
    MeasurableSet (MembershipSet h z₀) :=
  membership_measurable_of_generic_codes h hh hc z₀ hz eval heval hrep F hF
    (analyticSet_membershipSet h hh z₀ hz) hbound

end BorelWitness
end NoBorelUpperBoundFSigma

end
end
-- END COMPLETE MODULE NoBorelUpperBound.CategoryAnalytic

-- BEGIN COMPLETE MODULE NoBorelUpperBound.BaireContinuity
section
                                        
                                                       
                                            

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v

/-- A Borel map admits a countable array of open dense-point tests which are
correct simultaneously outside a meager set. No uniform bound on Borel ranks
is required. -/
theorem exists_open_generic_approximation
    {G : Type u} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    {Y : Type v} [PseudoMetricSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (f : G → Y) (hf : Measurable f) (y : ℕ → Y) (hy : DenseRange y)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ U : ℕ → ℕ → Set G, (∀ n j, IsOpen (U n j)) ∧
      ∀ᶠ g in residual G, ∀ n,
        (∃ j, g ∈ U n j) ∧ (∀ j, g ∈ U n j → dist (y j) (f g) < ε n) := by
  classical
  have htest (n j : ℕ) :
      ∃ U : Set G, IsOpen U ∧ {g | dist (y j) (f g) < ε n} =ᵇ U := by
    have hB : MeasurableSet {g | dist (y j) (f g) < ε n} := by
      have hO : IsOpen {q : Y | dist (y j) q < ε n} :=
        isOpen_lt (continuous_const.dist continuous_id) continuous_const
      exact hO.measurableSet.preimage hf
    exact hB.residualEq_isOpen
  choose U hU heq using htest
  refine ⟨U,hU,?_⟩
  have hag : ∀ᶠ g in residual G, ∀ n j,
      dist (y j) (f g) < ε n ↔ g ∈ U n j := by
    apply eventually_countable_forall.mpr
    intro n
    apply eventually_countable_forall.mpr
    intro j
    exact eventuallyEq_set.mp (heq n j)
  filter_upwards [hag] with g hg
  intro n
  refine ⟨?_,fun j hj => (hg n j).mpr hj⟩
  obtain ⟨j,hj⟩ := hy.exists_dist_lt (f g) (hε n)
  exact ⟨j,(hg n j).mp (by simpa only [dist_comm] using hj)⟩

/-- Distances bounded by a sequence tending to zero imply convergence. -/
theorem tendsto_of_dist_lt_approximation
    {Y : Type v} [PseudoMetricSpace Y] (s : ℕ → Y) (y : Y)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hs : ∀ n, dist (s n) y < ε n) : Tendsto s atTop (𝓝 y) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have he : ∀ᶠ n in atTop, ε n < δ := (tendsto_order.1 hε).2 δ hδ
  exact he.mono (fun n hn => lt_trans (hs n) hn)

end NoBorelUpperBoundFSigma

end
end
-- END COMPLETE MODULE NoBorelUpperBound.BaireContinuity

-- BEGIN COMPLETE MODULE NoBorelUpperBound.BorelEvaluator
section
                                                                    
                                                          
                                          

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter TopologicalSpace Topology MeasureTheory

namespace NoBorelUpperBoundFSigma.BorelCodes

variable (G : Type*) [TopologicalSpace G] [SecondCountableTopology G]

/-- Countably many open sets, coded using a fixed countable topological basis. -/
def Code := (ℕ × ℕ × countableBasis G) → Bool

instance : TopologicalSpace (Code G) := inferInstanceAs (TopologicalSpace ((_ × _ × _) → Bool))
instance : PolishSpace (Code G) where
  toSecondCountableTopology := inferInstanceAs (SecondCountableTopology ((_ × _ × _) → Bool))
  toIsCompletelyMetrizableSpace := inferInstanceAs
    (IsCompletelyMetrizableSpace ((_ × _ × _) → Bool))
instance : MeasurableSpace (Code G) := borel (Code G)
instance : BorelSpace (Code G) := ⟨rfl⟩

variable {G}

def eligible (c : Code G) (g : G) (n j : ℕ) : Prop :=
  ∃ b : countableBasis G, c (n,j,b) = true ∧ g ∈ (b : Set G)

private theorem exists_candidate (c : Code G) (g : G) (n : ℕ) :
    ∃ j, eligible c g n j ∨ ¬ ∃ k, eligible c g n k := by
  by_cases h : ∃ j, eligible c g n j
  · obtain ⟨j,hj⟩ := h
    exact ⟨j,Or.inl hj⟩
  · exact ⟨0,Or.inr h⟩

def selected (c : Code G) (g : G) (n : ℕ) : ℕ := Nat.find (exists_candidate c g n)

theorem eligible_selected (c : Code G) (g : G) (n : ℕ)
    (h : ∃ j, eligible c g n j) : eligible c g n (selected c g n) := by
  exact (Nat.find_spec (exists_candidate c g n)).resolve_right (not_not.mpr h)

variable [MeasurableSpace G] [BorelSpace G]

theorem measurableSet_eligible (n j : ℕ) :
    MeasurableSet {p : Code G × G | eligible p.1 p.2 n j} := by
  have hb (b : countableBasis G) : MeasurableSet
      {p : Code G × G | p.1 (n,j,b) = true ∧ p.2 ∈ (b : Set G)} := by
    have hc : Measurable (fun c : Code G => c (n,j,b)) :=
      (show Continuous (fun c : Code G => c (n,j,b)) from continuous_apply _).measurable
    exact ((isClosed_discrete ({true} : Set Bool)).measurableSet.preimage
      (hc.comp measurable_fst)).inter
      ((isOpen_of_mem_countableBasis b.property).measurableSet.preimage measurable_snd)
  simpa only [eligible, setOf_exists] using MeasurableSet.iUnion hb

theorem measurable_selected (n : ℕ) :
    Measurable (fun p : Code G × G => selected p.1 p.2 n) := by
  apply measurable_find (fun p : Code G × G => exists_candidate p.1 p.2 n)
  intro j
  have hex : MeasurableSet {p : Code G × G | ∃ k, eligible p.1 p.2 n k} := by
    simpa only [setOf_exists] using
      MeasurableSet.iUnion (fun k => measurableSet_eligible (G := G) n k)
  exact (measurableSet_eligible n j).union hex.compl

variable {Y : Type*} [TopologicalSpace Y] [PolishSpace Y] [Nonempty Y]

def approximation (c : Code G) (g : G) (n : ℕ) : Y :=
  denseSeq Y (selected c g n)

def eval (c : Code G) (g : G) : Y :=
  limUnder atTop (fun n : ℕ => approximation c g n)

variable [MeasurableSpace Y] [BorelSpace Y]

theorem measurable_approximation (n : ℕ) :
    Measurable (fun p : Code G × G => (approximation p.1 p.2 n : Y)) := by
  exact (measurable_of_countable (denseSeq Y)).comp (measurable_selected n)

theorem measurable_eval :
    Measurable (fun p : Code G × G => (eval p.1 p.2 : Y)) := by
  exact (StronglyMeasurable.limUnder
    (fun n : ℕ => (measurable_approximation (Y := Y) (G := G) n).stronglyMeasurable)).measurable

end NoBorelUpperBoundFSigma.BorelCodes

end
end
-- END COMPLETE MODULE NoBorelUpperBound.BorelEvaluator

-- BEGIN COMPLETE MODULE NoBorelUpperBound.GenericRepresentation
section
                                        
                                       
                                                 

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter TopologicalSpace Topology MeasureTheory

namespace NoBorelUpperBoundFSigma.BorelCodes
universe u v

variable {G : Type u} [TopologicalSpace G] [SecondCountableTopology G]

/-- Encode an array of open tests by all basis sets contained in each test. -/
def codeOfOpenTests (U : ℕ → ℕ → Set G) : Code G :=
  fun q => decide ((q.2.2 : Set G) ⊆ U q.1 q.2.1)

theorem eligible_codeOfOpenTests_iff (U : ℕ → ℕ → Set G)
    (hU : ∀ n j, IsOpen (U n j)) (g : G) (n j : ℕ) :
    eligible (codeOfOpenTests U) g n j ↔ g ∈ U n j := by
  classical
  constructor
  · rintro ⟨b,hb,hg⟩
    have hbU : (b : Set G) ⊆ U n j := by
      simpa only [codeOfOpenTests,decide_eq_true_eq] using hb
    exact hbU hg
  · intro hg
    obtain ⟨b,hb,hgb,hbU⟩ :=
      (isBasis_countableBasis G).exists_subset_of_mem_open hg (hU n j)
    exact ⟨⟨b,hb⟩,by simpa only [codeOfOpenTests,decide_eq_true_eq] using hbU,hgb⟩

/-- The fixed Borel evaluator represents every Borel map outside a meager
set. This concerns agreement modulo category, so Borel ranks need not be
bounded by a common ordinal. -/
theorem exists_code_residual_eq
    [MeasurableSpace G] [BorelSpace G]
    {Y : Type v} [TopologicalSpace Y] [PolishSpace Y] [Nonempty Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (f : G → Y) (hf : Measurable f) :
    ∃ c : Code G, ∀ᶠ g in residual G, eval c g = f g := by
  letI := upgradeIsCompletelyMetrizable Y
  obtain ⟨U,hU,hag⟩ := NoBorelUpperBoundFSigma.exists_open_generic_approximation
    f hf (denseSeq Y) (denseRange_denseSeq Y)
    (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
    (fun n => div_pos zero_lt_one (by positivity))
  refine ⟨codeOfOpenTests U, hag.mono ?_⟩
  intro g hg
  change limUnder atTop (fun n : ℕ => (approximation (codeOfOpenTests U) g n : Y)) = f g
  apply Filter.Tendsto.limUnder_eq
  apply NoBorelUpperBoundFSigma.tendsto_of_dist_lt_approximation _ _
    (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
    tendsto_one_div_add_atTop_nhds_zero_nat
  intro n
  apply (hg n).2
  apply (eligible_codeOfOpenTests_iff U hU g n _).mp
  apply eligible_selected
  obtain ⟨j,hj⟩ := (hg n).1
  exact ⟨j,(eligible_codeOfOpenTests_iff U hU g n j).mpr hj⟩

/-- Topological Borel-measurability version used by the mission definitions. -/
theorem exists_code_of_isBorelMeasurable
    [MeasurableSpace G] [BorelSpace G]
    {Y : Type v} [TopologicalSpace Y] [PolishSpace Y] [Nonempty Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (f : G → Y) (hf : NoUniversalFSigma.IsBorelMeasurable f) :
    ∃ c : Code G, ∀ᶠ g in residual G, eval c g = f g := by
  apply exists_code_residual_eq f
  unfold NoUniversalFSigma.IsBorelMeasurable at hf
  rwa [← BorelSpace.measurable_eq,← BorelSpace.measurable_eq] at hf

end NoBorelUpperBoundFSigma.BorelCodes

end
end
-- END COMPLETE MODULE NoBorelUpperBound.GenericRepresentation

-- BEGIN COMPLETE MODULE NoBorelUpperBound.CategoryTransferFinal
section
                                         
                                              

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v w z

/-- Generic homomorphism category transfer, for a standard Borel parameter
space and countably many continuously parametrized Polish-group generators.
The Borel evaluator and the finite-word analytic membership witnesses are
constructed in the proof rather than assumed. -/
theorem category_transfer
    {P : Type u} [MeasurableSpace P] [StandardBorelSpace P]
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]
    {A : ℕ → Type w} [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)]
    [∀ n, IsTopologicalGroup (A n)] [∀ n, PolishSpace (A n)]
    [∀ n, MeasurableSpace (A n)] [∀ n, BorelSpace (A n)]
    {Y : Type z} [TopologicalSpace Y] [PolishSpace Y]
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2))
    (hc : ∀ n p, Continuous (h n p))
    (z₀ : P → G) (hz : Measurable z₀)
    (F : Setoid Y) (hF : IsBorelRelation F.r)
    (hbound : ∀ p, p ∉ MembershipSet h z₀ →
      BorelReducible (GroupCosetRelation (GeneratedSubgroup h p)) F.r) :
    MeasurableSet (MembershipSet h z₀) := by
  classical
  letI := upgradeStandardBorel P
  letI : MeasurableSpace Y := borel Y
  letI : BorelSpace Y := ⟨rfl⟩
  by_cases hfull : ∀ p, p ∈ MembershipSet h z₀
  · have heq : MembershipSet h z₀ = univ := by ext p; simp [hfull p]
    rw [heq]
    exact MeasurableSet.univ
  · obtain ⟨p,hp⟩ := not_forall.mp hfull
    obtain ⟨f,_,_⟩ := hbound p hp
    letI : Nonempty Y := ⟨f 1⟩
    exact category_transfer_of_generic_codes h hh hc z₀ hz
      (BorelCodes.eval (Y := Y)) BorelCodes.measurable_eval
      BorelCodes.exists_code_of_isBorelMeasurable F hF hbound

end NoBorelUpperBoundFSigma

end
end
-- END COMPLETE MODULE NoBorelUpperBound.CategoryTransferFinal

-- BEGIN COMPLETE MODULE NoBorelUpperBound.Main
section
                                           
                                              

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v

/-- A common upper bound has nonempty underlying space, since even the
one-point equivalence relation must reduce to it. -/
theorem nonempty_of_isFSigmaUpperBound {Y : Type u} [TopologicalSpace Y]
    {F : Y → Y → Prop} (hF : IsFSigmaUpperBound F) : Nonempty Y := by
  let E : Setoid Unit := ⟨fun _ _ => True,⟨fun _ => trivial,
    fun _ => trivial,fun _ _ => trivial⟩⟩
  have hE : NoUniversalFSigma.IsFSigmaRelation E.r := by
    refine ⟨fun _ => Set.univ,fun _ => isClosed_univ,?_⟩
    ext p
    simp [E]
  obtain ⟨f,_,_⟩ := hF Unit E hE
  exact ⟨f ()⟩

/-- The explicit tree construction contradicts a Borel common upper bound. -/
theorem not_isFSigmaUpperBound
    {Y : Type u} [TopologicalSpace Y] [PolishSpace Y]
    (F : Setoid Y) (hF : IsBorelRelation F.r) : ¬ IsFSigmaUpperBound F.r := by
  intro hbound
  letI : MeasurableSpace Trees.TreeSpace := borel Trees.TreeSpace
  letI : BorelSpace Trees.TreeSpace := ⟨rfl⟩
  letI : MeasurableSpace Construction.G := borel Construction.G
  letI : BorelSpace Construction.G := ⟨rfl⟩
  letI : MeasurableSpace Construction.Axis := borel Construction.Axis
  letI : BorelSpace Construction.Axis := ⟨rfl⟩
  have hm := category_transfer Construction.family
    (fun n => (Construction.continuous_family n).measurable)
    Construction.continuous_family_fixed (fun _ => Construction.designated)
    measurable_const F hF
    (by
      intro T hT
      rw [Construction.generatedSubgroup_family]
      have hT' : ¬ Trees.HasBranch T := by
        simpa only [Construction.membershipSet_family,Trees.IF,mem_setOf_eq] using hT
      exact hbound Construction.G (Construction.cosetSetoid (TreeOperators.operator T))
        (Construction.isFSigma_cosetGraph _
          (TreeOperators.operator_injective_of_not_hasBranch T hT')))
  rw [Construction.membershipSet_family] at hm
  exact Trees.not_borel_IF hm

/-- Main Theorem 1: no Borel equivalence relation on a Polish space is an
upper bound under Borel reducibility for all F-sigma equivalence relations. -/
theorem theorem1 {Y : Type u} [TopologicalSpace Y] [PolishSpace Y] :
    ¬ ∃ F : Setoid Y, IsBorelRelation F.r ∧ IsFSigmaUpperBound F.r := by
  rintro ⟨F,hF,hbound⟩
  exact not_isFSigmaUpperBound F hF hbound

end NoBorelUpperBoundFSigma

end
end
-- END COMPLETE MODULE NoBorelUpperBound.Main

-- BEGIN COMPLETE MODULE ModNullProof.OrdinaryUnbounded
section
                                
                                
                             

set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace

namespace ModNullUniversality.LinearCosets

open NoBorelUpperBoundFSigma
open NoBorelUpperBoundFSigma.Construction
open NoBorelUpperBoundFSigma.SymmetricTensor

def productSetoid (F : StandardBorelEquivalence) : Setoid ((A × A) × F.Carrier) where
  r x y := x.1 = y.1 ∧ F.rel x.2 y.2
  iseqv := ⟨fun x => ⟨rfl,F.equivalence.refl x.2⟩,
    fun h => ⟨h.1.symm,F.equivalence.symm h.2⟩,
    fun h k => ⟨h.1.trans k.1,F.equivalence.trans h.2 k.2⟩⟩

/-- The actual tree-tensor coset family has no Borel upper bound. -/
theorem tensor_family_unbounded (F : StandardBorelEquivalence) :
    ∃ T : WF, ¬ ModNullUniversality.BorelReducible
      (TensorRelation (TreeOperators.operator T.val.val)) F.rel := by
  classical
  by_contra! hbound
  letI := upgradeStandardBorel F.Carrier
  letI : MeasurableSpace A := borel A
  letI : BorelSpace A := ⟨rfl⟩
  letI : MeasurableSpace Trees.TreeSpace := borel Trees.TreeSpace
  letI : BorelSpace Trees.TreeSpace := ⟨rfl⟩
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  letI : MeasurableSpace Axis := borel Axis
  letI : BorelSpace Axis := ⟨rfl⟩
  let P := (A × A) × F.Carrier
  let R : Setoid P := productSetoid F
  have hR : IsBorelRelation R.r := by
    have heq : MeasurableSet {p : P × P | p.1.1 = p.2.1} :=
      (isClosed_eq (continuous_fst.fst : Continuous (fun p : P×P => p.1.1))
        continuous_snd.fst).measurableSet
    have hF : MeasurableSet {p : P × P | F.rel p.1.2 p.2.2} :=
      F.measurable_graph.preimage (measurable_fst.snd.prodMk measurable_snd.snd)
    change @MeasurableSet (P × P) (borel (P × P)) _
    have hB : (inferInstance : MeasurableSpace (P × P)) = borel (P × P) :=
      BorelSpace.measurable_eq
    rw [← hB]
    exact heq.inter hF
  have hnil : ∀ T : Trees.TreeSpace, T ∉ MembershipSet family (fun _ => designated) →
      NoBorelUpperBoundFSigma.BorelReducible
        (GroupCosetRelation (GeneratedSubgroup family T)) R.r := by
    intro T hT
    have hnb : ¬ Trees.HasBranch T := by
      simpa only [membershipSet_family,Trees.IF,mem_setOf_eq] using hT
    let W : WF := ⟨T,hnb⟩
    obtain ⟨f,hf,hred⟩ := hbound W
    let D := TreeOperators.operator T
    let g : G → P := fun x => ((theta D x).1,f (theta D x).2)
    have hg : Measurable g :=
      ((continuous_fst.comp (continuous_theta D)).measurable).prodMk
        (hf.comp (continuous_snd.comp (continuous_theta D)).measurable)
    refine ⟨g,?_,?_⟩
    · change @Measurable G P (borel G) (borel P) g
      have hB : (inferInstance : MeasurableSpace P) = borel P := BorelSpace.measurable_eq
      rw [← hB]
      exact hg
    · intro x y
      rw [generatedSubgroup_family]
      change GroupCosetRelation (subgroup D) x y ↔ _
      rw [coset_iff_theta]
      exact and_congr_right (fun _ => hred _ _)
  have hm := category_transfer family (fun n => (continuous_family n).measurable)
    continuous_family_fixed (fun _ => designated) measurable_const R hR hnil
  rw [membershipSet_family] at hm
  exact Trees.not_borel_IF hm

end ModNullUniversality.LinearCosets

namespace ModNullUniversality.CompactTensor

theorem source_family_unbounded (F : StandardBorelEquivalence) :
    ∃ T : WF, ¬ BorelReducible (sourceRelation T) F.rel := by
  exact LinearCosets.tensor_family_unbounded F

end ModNullUniversality.CompactTensor

end
end
-- END COMPLETE MODULE ModNullProof.OrdinaryUnbounded

-- BEGIN COMPLETE MODULE ModNullProof.CompactUnbounded
section
                                 
                                     

set_option autoImplicit false
noncomputable section

namespace ModNullUniversality.CompactTensor

theorem compact_family_unbounded (F : StandardBorelEquivalence) :
    ∃ T : WF, ¬ BorelReducible
      (CosetRelation compactGroup (compactSubgroup (tensorSubspace T))) F.rel := by
  obtain ⟨T,hT⟩ := source_family_unbounded F
  refine ⟨T,?_⟩
  rintro ⟨f,hf,hred⟩
  obtain ⟨g,hg,hgrel⟩ := source_reduces_compact T
  apply hT
  exact ⟨f ∘ g,hf.comp hg,fun x y => (hgrel x y).trans (hred (g x) (g y))⟩

end ModNullUniversality.CompactTensor

end
end
-- END COMPLETE MODULE ModNullProof.CompactUnbounded

-- BEGIN COMPLETE MODULE ModNullProof.CoordinateBounds
section
                               
                                           
                                                
                                                         

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace ModNullUniversality.CompactTensor
open NoBorelUpperBoundFSigma.L1Coordinates

/-- The closed coordinate-topology ball of the scalar plus matrix l1 norm. -/
def coordinateBall (M : ℝ) : Set Ambient :=
  {u | ∀ t : Finset Index, ∑ i ∈ t, |u i| ≤ M}

theorem isClosed_coordinateBall (M : ℝ) : IsClosed (coordinateBall M) := by
  change IsClosed {u : Ambient | ∀ t : Finset Index, ∑ i ∈ t, |u i| ≤ M}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro t
  exact isClosed_le (continuous_finsetSum _ (fun i _ => (continuous_apply i).abs)) continuous_const

theorem coordinateBall_coordinate_le (M : ℝ) {u : Ambient}
    (hu : u ∈ coordinateBall M) (i : Index) : |u i| ≤ M := by
  have h := hu ({i} : Finset Index)
  simpa only [Finset.sum_singleton] using h

theorem isCompact_coordinateBall (M : ℝ) : IsCompact (coordinateBall M) := by
  have hc : IsCompact {u : Ambient | ∀ i, u i ∈ Icc (-M) M} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  apply hc.of_isClosed_subset (isClosed_coordinateBall M)
  intro u hu i
  exact abs_le.mp (coordinateBall_coordinate_le M hu i)

theorem summable_coordinates (p : Space) : Summable (fun i : Index => |coordinates p i|) := by
  apply Summable.sum
  · exact (hasSum_fintype _).summable
  · simpa only [Function.comp_def,coordinates_right,Real.norm_eq_abs] using summable_norm p.2

theorem exists_coordinateBall (p : Space) : ∃ M : ℕ, coordinates p ∈ coordinateBall M := by
  obtain ⟨M,hM⟩ := exists_nat_ge (∑' i : Index, |coordinates p i|)
  refine ⟨M,fun t => ?_⟩
  exact ((summable_coordinates p).sum_le_tsum t (fun _ _ => abs_nonneg _)).trans hM

def ballMatrix (M : ℝ) (u : coordinateBall M) : MatrixL1 S S :=
  ⟨fun ij => u.val (.inr ij), memℓp_gen' (C := M) (by
    intro t
    have h := u.property (t.image Sum.inr)
    rw [Finset.sum_image] at h
    · simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs] using h
    · intro a ha b hb hab
      exact Sum.inr.inj hab)⟩

def ballSource (M : ℝ) (u : coordinateBall M) : Space :=
  (u.val (.inl ()),ballMatrix M u)

@[simp] theorem ballMatrix_apply (M : ℝ) (u : coordinateBall M) (ij : S × S) :
    ballMatrix M u ij = u.val (.inr ij) := rfl

theorem coordinates_ballSource (M : ℝ) (u : coordinateBall M) :
    coordinates (ballSource M u) = u.val := by
  funext i
  cases i with
  | inl j => cases j; rfl
  | inr ij => rfl

@[simp] theorem ballSource_coordinates (M : ℝ) (p : Space)
    (hp : coordinates p ∈ coordinateBall M) :
    ballSource M ⟨coordinates p,hp⟩ = p :=
  coordinates_injective (coordinates_ballSource M _)

theorem coordinateBall_subset_range (M : ℝ) : coordinateBall M ⊆ range coordinates := by
  intro u hu
  exact ⟨ballSource M ⟨u,hu⟩,coordinates_ballSource M _⟩

end ModNullUniversality.CompactTensor

end
end
-- END COMPLETE MODULE ModNullProof.CoordinateBounds

-- BEGIN COMPLETE MODULE ModNullProof.BaireOneComplexity
section
                                   
                                        
                                             

set_option autoImplicit false
noncomputable section

open Set Filter TopologicalSpace
open scoped Topology BigOperators

namespace ModNullUniversality

/-- A real function obtained as the pointwise limit of a sequence of continuous functions. -/
def BaireOne {X : Type*} [TopologicalSpace X] (f : X → ℝ) : Prop :=
  ∃ g : ℕ → X → ℝ, (∀ n, Continuous (g n)) ∧
    ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x))

namespace BaireOne

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {f g : X → ℝ}

theorem of_continuous (hf : Continuous f) : BaireOne f :=
  ⟨fun _ => f,fun _ => hf,fun _ => tendsto_const_nhds⟩

theorem const (c : ℝ) : BaireOne (fun _ : X => c) :=
  of_continuous continuous_const

theorem add (hf : BaireOne f) (hg : BaireOne g) : BaireOne (fun x => f x + g x) := by
  obtain ⟨a,ha,ha'⟩ := hf
  obtain ⟨b,hb,hb'⟩ := hg
  exact ⟨fun n x => a n x + b n x,fun n => (ha n).add (hb n),
    fun x => (ha' x).add (hb' x)⟩

theorem neg (hf : BaireOne f) : BaireOne (fun x => -f x) := by
  obtain ⟨a,ha,ha'⟩ := hf
  exact ⟨fun n x => -a n x,fun n => (ha n).neg,fun x => (ha' x).neg⟩

theorem sub (hf : BaireOne f) (hg : BaireOne g) : BaireOne (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : BaireOne f) (hg : BaireOne g) : BaireOne (fun x => f x * g x) := by
  obtain ⟨a,ha,ha'⟩ := hf
  obtain ⟨b,hb,hb'⟩ := hg
  exact ⟨fun n x => a n x * b n x,fun n => (ha n).mul (hb n),
    fun x => (ha' x).mul (hb' x)⟩

theorem smul (hf : BaireOne f) (c : ℝ) : BaireOne (fun x => c * f x) :=
  (const c).mul hf

theorem comp_continuous (hf : BaireOne f) (h : Y → X) (hh : Continuous h) :
    BaireOne (fun y => f (h y)) := by
  obtain ⟨a,ha,ha'⟩ := hf
  exact ⟨fun n y => a n (h y),fun n => (ha n).comp hh,fun y => ha' (h y)⟩

/-- Continuous operations on any family of real Baire-one functions remain Baire one. -/
theorem continuous_operation {ι : Type*} {a : X → ι → ℝ}
    (ha : ∀ i, BaireOne (fun x => a x i)) {p : (ι → ℝ) → ℝ} (hp : Continuous p) :
    BaireOne (fun x => p (a x)) := by
  classical
  choose b hb hb' using ha
  refine ⟨fun n x => p (fun i => b i n x),fun n => ?_,fun x => ?_⟩
  · exact hp.comp (continuous_pi (fun i => hb i n))
  · exact hp.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (fun i => hb' i x))

theorem sum {ι : Type*} (s : Finset ι) {a : ι → X → ℝ}
    (ha : ∀ i ∈ s, BaireOne (a i)) : BaireOne (fun x => ∑ i ∈ s, a i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (X := X) 0)
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (ha i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

theorem prod {ι : Type*} (s : Finset ι) {a : ι → X → ℝ}
    (ha : ∀ i ∈ s, BaireOne (a i)) : BaireOne (fun x => ∏ i ∈ s, a i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (X := X) 1)
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      (ha i (Finset.mem_insert_self i s)).mul
        (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

theorem matrix_det {n : Type*} [Fintype n] [DecidableEq n] {a : X → Matrix n n ℝ}
    (ha : ∀ i j, BaireOne (fun x => a x i j)) : BaireOne (fun x => (a x).det) := by
  exact continuous_operation (a := fun x (ij : n × n) => a x ij.1 ij.2)
    (fun ij => ha ij.1 ij.2)
    ((continuous_pi (fun i => continuous_pi (fun j => continuous_apply (i,j)))).matrix_det)

theorem matrix_adjugate {n : Type*} [Fintype n] [DecidableEq n] {a : X → Matrix n n ℝ}
    (ha : ∀ i j, BaireOne (fun x => a x i j)) (i j : n) :
    BaireOne (fun x => (a x).adjugate i j) := by
  have hc : Continuous (fun v : n × n → ℝ => fun i j => v (i,j)) :=
    continuous_pi (fun i => continuous_pi (fun j => continuous_apply (i,j)))
  exact continuous_operation (a := fun x (ij : n × n) => a x ij.1 ij.2)
    (fun ij => ha ij.1 ij.2) (hc.matrix_adjugate.matrix_elem i j)

theorem isFSigma_lt (hf : BaireOne f) (a : ℝ) : IsFSigma {x | f x < a} := by
  obtain ⟨u,hu,hlim⟩ := hf
  let C : ℕ → ℕ → Set X := fun k N => ⋂ n ≥ N, {x | u n x ≤ a - 1 / (k + 1 : ℝ)}
  have hC : ∀ k N, IsClosed (C k N) := by
    intro k N
    exact isClosed_iInter (fun n => isClosed_iInter (fun _ =>
      isClosed_le (hu n) continuous_const))
  have hseq : {x | f x < a} = ⋃ k : ℕ, ⋃ N : ℕ, C k N := by
    ext x
    simp only [mem_setOf_eq,mem_iUnion]
    constructor
    · intro hx
      obtain ⟨k,hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      have hsmall : f x < a - 1 / (k + 1 : ℝ) := by linarith
      obtain ⟨N,hN⟩ := eventually_atTop.mp
        ((tendsto_order.mp (hlim x)).2 _ hsmall)
      exact ⟨k,N,by simpa only [C,mem_iInter,mem_setOf_eq] using
        (fun n hn => (hN n hn).le)⟩
    · rintro ⟨k,N,hx⟩
      have hN : ∀ n ≥ N, u n x ≤ a - 1 / (k + 1 : ℝ) := by
        simpa only [C,mem_iInter,mem_setOf_eq] using hx
      have hle := le_of_tendsto (hlim x) (eventually_atTop.mpr ⟨N,hN⟩)
      have hpos : 0 < 1 / (k + 1 : ℝ) := by positivity
      linarith
  rw [hseq]
  exact isFSigma_iUnion_nat (fun k => ⟨C k,hC k,rfl⟩)

theorem isFSigma_gt (hf : BaireOne f) (a : ℝ) : IsFSigma {x | a < f x} := by
  simpa only [neg_lt_neg_iff] using hf.neg.isFSigma_lt (-a)

theorem isFSigma_Ioo (hf : BaireOne f) (a b : ℝ) : IsFSigma (f ⁻¹' Ioo a b) := by
  exact isFSigma_inter (hf.isFSigma_gt a) (hf.isFSigma_lt b)

/-- The defining preimage characterization of real Baire-one functions. -/
theorem isFSigma_preimage_open (hf : BaireOne f) {U : Set ℝ} (hU : IsOpen U) :
    IsFSigma (f ⁻¹' U) := by
  let I := {p : ℚ × ℚ // Ioo (p.1 : ℝ) (p.2 : ℝ) ⊆ U}
  have heq : f ⁻¹' U = ⋃ p : I, f ⁻¹' Ioo (p.val.1 : ℝ) (p.val.2 : ℝ) := by
    ext x
    simp only [mem_preimage,mem_iUnion]
    constructor
    · intro hx
      obtain ⟨l,r,hlr,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hx)
      obtain ⟨a,hla,hax⟩ := exists_rat_btwn hlr.1
      obtain ⟨b,hxb,hbr⟩ := exists_rat_btwn hlr.2
      refine ⟨⟨(a,b),?_⟩,hax,hxb⟩
      exact fun y hy => hsub ⟨hla.trans hy.1,hy.2.trans hbr⟩
    · rintro ⟨p,hp⟩
      exact p.property hp
  rw [heq]
  exact isFSigma_iUnion (fun p => hf.isFSigma_Ioo _ _)

theorem isGdelta_zero (hf : BaireOne f) : IsGδ {x | f x = 0} := by
  have h := isGdelta_compl_of_isFSigma
    (hf.isFSigma_preimage_open (isClosed_singleton.isOpen_compl : IsOpen ({0} : Set ℝ)ᶜ))
  simpa only [preimage_compl,compl_compl] using h

theorem isGdelta_eq (hf : BaireOne f) (hg : BaireOne g) : IsGδ {x | f x = g x} := by
  simpa only [sub_eq_zero] using (hf.sub hg).isGdelta_zero

theorem isFSigma_ne_zero (hf : BaireOne f) : IsFSigma {x | f x ≠ 0} := by
  exact isFSigma_compl_of_isGdelta hf.isGdelta_zero

theorem isFSigma_ne (hf : BaireOne f) (hg : BaireOne g) : IsFSigma {x | f x ≠ g x} := by
  exact isFSigma_compl_of_isGdelta (hf.isGdelta_eq hg)

end BaireOne
end ModNullUniversality

end
end
-- END COMPLETE MODULE ModNullProof.BaireOneComplexity

-- BEGIN COMPLETE MODULE ModNullProof.WeakTensorCoordinates
section
                                    
                                      
                                             
                               
                                                  

set_option autoImplicit false
noncomputable section
open Set Filter Matrix
open scoped Topology BigOperators

namespace ModNullUniversality.CompactTensor
open NoBorelUpperBoundFSigma.L1Coordinates
open NoBorelUpperBoundFSigma.SymmetricTensor

/-- The finite-coordinate approximations to a bounded operator's row evaluation. -/
def rowApprox (D : L1 S →L[ℝ] L1 S) (M : ℝ) (a q : S) (n : ℕ)
    (u : coordinateBall M) : ℝ :=
  ∑ k ∈ Finset.range n, D (lp.single 1 (Equiv.listNatEquivNat.symm k)
    (u.val (.inr (a,Equiv.listNatEquivNat.symm k)))) q

theorem continuous_rowApprox (D : L1 S →L[ℝ] L1 S) (M : ℝ) (a q : S) (n : ℕ) :
    Continuous (rowApprox D M a q n) := by
  apply continuous_finsetSum
  intro k hk
  exact (lp.evalCLM ℝ (fun _ : S => ℝ) 1 q).continuous.comp
    (D.continuous.comp ((lp.singleContinuousLinearMap ℝ (fun _ : S => ℝ) 1
      (Equiv.listNatEquivNat.symm k)).continuous.comp
        ((continuous_apply _).comp continuous_subtype_val)))

theorem tendsto_rowApprox (D : L1 S →L[ℝ] L1 S) (M : ℝ) (a q : S)
    (u : coordinateBall M) :
    Tendsto (fun n => rowApprox D M a q n u) atTop
      (𝓝 (D (NoBorelUpperBoundFSigma.L1Coordinates.row a (ballMatrix M u)) q)) := by
  have h := (lp.hasSum_single (by simp : (1 : ENNReal) ≠ ⊤)
    (NoBorelUpperBoundFSigma.L1Coordinates.row a (ballMatrix M u))).mapL D
  have h' := h.mapL (lp.evalCLM ℝ (fun _ : S => ℝ) 1 q)
  have h'' := Equiv.listNatEquivNat.symm.hasSum_iff.mpr h'
  exact h''.tendsto_sum_nat

theorem baireOne_row (D : L1 S →L[ℝ] L1 S) (M : ℝ) (a q : S) :
    BaireOne (fun u : coordinateBall M =>
      D (NoBorelUpperBoundFSigma.L1Coordinates.row a (ballMatrix M u)) q) :=
  ⟨rowApprox D M a q,continuous_rowApprox D M a q,tendsto_rowApprox D M a q⟩

theorem baireOne_matrix (M : ℝ) (ij : S × S) :
    BaireOne (fun u : coordinateBall M => ballMatrix M u ij) := by
  change BaireOne (fun u : coordinateBall M => u.val (Sum.inr ij))
  exact BaireOne.of_continuous ((continuous_apply (Sum.inr ij : Index)).comp continuous_subtype_val)

theorem baireOne_scalar (M : ℝ) :
    BaireOne (fun u : coordinateBall M => (ballSource M u).1) :=
  BaireOne.of_continuous ((continuous_apply _).comp continuous_subtype_val)

theorem baireOne_pivotDet (D : L1 S →L[ℝ] L1 S) (M : ℝ) {r : ℕ}
    (rows qs : Fin r → S) :
    BaireOne (fun u : coordinateBall M => (pivotD D rows qs (ballMatrix M u)).det) :=
  BaireOne.matrix_det (fun i j => baireOne_row D M (rows j) (qs i))

theorem baireOne_pivotAdjugate (D : L1 S →L[ℝ] L1 S) (M : ℝ) {r : ℕ}
    (rows qs : Fin r → S) (i j : Fin r) :
    BaireOne (fun u : coordinateBall M => (pivotD D rows qs (ballMatrix M u)).adjugate i j) :=
  BaireOne.matrix_adjugate (fun i j => baireOne_row D M (rows j) (qs i)) i j

theorem baireOne_lift (D : L1 S →L[ℝ] L1 S) (M : ℝ) {r : ℕ}
    (rows qs : Fin r → S) (i j : S) :
    BaireOne (fun u : coordinateBall M => liftNumerator D rows qs (ballMatrix M u) (i,j)) := by
  simp_rw [liftNumerator_apply]
  exact BaireOne.sum Finset.univ (fun t ht => BaireOne.sum Finset.univ
    (fun s hs => (baireOne_pivotAdjugate D M rows qs t s).mul
      ((baireOne_matrix M (rows t,i)).mul (baireOne_matrix M (qs s,j)))))

theorem mapLeft_liftNumerator_apply (D : L1 S →L[ℝ] L1 S) {r : ℕ}
    (rows qs : Fin r → S) (R : MatrixL1 S S) (i j : S) :
    mapLeft D (liftNumerator D rows qs R) (i,j) =
      ∑ t, ∑ s, (pivotD D rows qs R).adjugate t s *
        (D (NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R) i * R (qs s,j)) := by
  change (lp.evalCLM ℝ (fun _ : S×S => ℝ) 1 (i,j))
    (mapLeft D (liftNumerator D rows qs R)) = _
  simp only [liftNumerator,map_sum,map_smul,smul_eq_mul,mapLeft_outer]
  rfl

theorem baireOne_mapLeft_lift (D : L1 S →L[ℝ] L1 S) (M : ℝ) {r : ℕ}
    (rows qs : Fin r → S) (i j : S) :
    BaireOne (fun u : coordinateBall M =>
      mapLeft D (liftNumerator D rows qs (ballMatrix M u)) (i,j)) := by
  simp_rw [mapLeft_liftNumerator_apply]
  exact BaireOne.sum Finset.univ (fun t ht => BaireOne.sum Finset.univ
    (fun s hs => (baireOne_pivotAdjugate D M rows qs t s).mul
      ((baireOne_row D M (rows t) i).mul (baireOne_matrix M (qs s,j)))))

end ModNullUniversality.CompactTensor

end
end
-- END COMPLETE MODULE ModNullProof.WeakTensorCoordinates

-- BEGIN COMPLETE MODULE ModNullProof.WeakTensorRank
section
                                    
                                            
                                                    
                                    

set_option autoImplicit false
noncomputable section
open Set Matrix
open scoped BigOperators

namespace ModNullUniversality.CompactTensor
open NoBorelUpperBoundFSigma.L1Coordinates
open NoBorelUpperBoundFSigma.SymmetricTensor
open NoBorelUpperBoundFSigma.TensorAlgebra

/-- Rank at most r, expressed solely by vanishing finite coordinate minors. -/
def RankLE (r : ℕ) (u : Ambient) : Prop :=
  ∀ rows cols : Fin (r+1) → S,
    Matrix.det (fun i j => u (.inr (rows i,cols j))) = 0

theorem isClosed_rankLE (r : ℕ) : IsClosed {u : Ambient | RankLE r u} := by
  simp only [RankLE,setOf_forall]
  apply isClosed_iInter
  intro rows
  apply isClosed_iInter
  intro cols
  apply isClosed_eq _ continuous_const
  have hc : Continuous (fun u : Ambient =>
      fun i j : Fin (r+1) => u (.inr (rows i,cols j))) :=
    continuous_pi (fun i => continuous_pi (fun j => continuous_apply _))
  exact hc.matrix_det

theorem rankLE_not_independent (r : ℕ) (R : MatrixL1 S S)
    (hR : RankLE r (coordinates (0,R))) (rows : Fin (r+1) → S) :
    ¬ LinearIndependent ℝ (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R) := by
  intro hli
  have hcoord := independent_coordinates (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R) hli
  obtain ⟨cols,hdet⟩ := exists_coordinate_pivot (fun t j => R (rows t,j)) hcoord
  have hz := hR rows cols
  have heq : (fun i j => R (rows j,cols i)) =
      (fun i j => R (rows i,cols j))ᵀ := rfl
  change Matrix.det (fun i j : Fin (r+1) => R (rows j,cols i)) ≠ 0 at hdet
  rw [heq,Matrix.det_transpose] at hdet
  exact hdet hz

theorem finiteDimensional_rowSpace_rankLE (r : ℕ) (R : MatrixL1 S S)
    (hR : RankLE r (coordinates (0,R))) : FiniteDimensional ℝ (rowSpace R) := by
  classical
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℝ (fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R)
  have hf : Finite κ := by
    by_contra hfinite
    letI : Infinite κ := not_finite_iff_infinite.mp hfinite
    let e : Fin (r+1) → κ := fun i => Infinite.natEmbedding κ i.val
    have he : Function.Injective e := fun i j h => Fin.ext ((Infinite.natEmbedding κ).injective h)
    exact rankLE_not_independent r R hR (fun t => a (e t)) (hli.comp e he)
  letI := hf
  have hi : FiniteDimensional ℝ (Submodule.span ℝ (range ((fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R) ∘ a))) :=
    (Module.Basis.span hli).finiteDimensional_of_finite
  change FiniteDimensional ℝ (Submodule.span ℝ (range (fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R)))
  exact hspan ▸ hi

theorem finrank_rowSpace_le_rankLE (r : ℕ) (R : MatrixL1 S S)
    (hR : RankLE r (coordinates (0,R))) : Module.finrank ℝ (rowSpace R) ≤ r := by
  classical
  letI := finiteDimensional_rowSpace_rankLE r R hR
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℝ (fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R)
  letI : FiniteDimensional ℝ (Submodule.span ℝ (range ((fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R) ∘ a))) :=
    hspan.symm ▸ finiteDimensional_rowSpace_rankLE r R hR
  letI : Fintype κ := FiniteDimensional.fintypeBasisIndex (Module.Basis.span hli)
  have hcard : Fintype.card κ ≤ r := by
    by_contra h
    have hemb : Fintype.card (Fin (r+1)) ≤ Fintype.card κ := by
      simpa using Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hemb
    exact rankLE_not_independent r R hR (fun t => a (e t)) (hli.comp e e.injective)
  have heq : Module.finrank ℝ (rowSpace R) = Fintype.card κ := by
    change Module.finrank ℝ (Submodule.span ℝ (range (fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R))) = _
    rw [← hspan]
    exact Module.finrank_eq_card_basis (Module.Basis.span hli)
  rw [heq]
  exact hcard

theorem exists_row_basis_of_finiteDimensional (R : MatrixL1 S S)
    [FiniteDimensional ℝ (rowSpace R)] :
    ∃ r : ℕ, ∃ rows : Fin r → S,
      LinearIndependent ℝ (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R) ∧
      Submodule.span ℝ (range (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R)) = rowSpace R := by
  classical
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℝ (fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R)
  letI : FiniteDimensional ℝ (Submodule.span ℝ (range ((fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R) ∘ a))) :=
    hspan.symm ▸ (inferInstance : FiniteDimensional ℝ (rowSpace R))
  letI : Fintype κ := FiniteDimensional.fintypeBasisIndex (Module.Basis.span hli)
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ,a ∘ e,hli.comp e e.injective,?_⟩
  have hr : range (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row ((a ∘ e) t) R) =
      range ((fun i => NoBorelUpperBoundFSigma.L1Coordinates.row i R) ∘ a) := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩; exact ⟨e t,rfl⟩
    · rintro ⟨k,rfl⟩
      obtain ⟨t,rfl⟩ := e.surjective k
      exact ⟨t,rfl⟩
  rw [hr]
  exact hspan

/-- Finite coordinate rank in an l1 matrix is actual finite tensor rank. -/
theorem mem_algebraicSpan_of_finiteDimensional (R : MatrixL1 S S)
    [FiniteDimensional ℝ (rowSpace R)] : R ∈ algebraicSpan := by
  classical
  obtain ⟨r,rows,hli,hspan⟩ := exists_row_basis_of_finiteDimensional R
  obtain ⟨cols,hdet⟩ := exists_coordinate_pivot
    (fun t j => R (rows t,j)) (independent_coordinates _ hli)
  let P : Matrix (Fin r) (Fin r) ℝ := fun i j => R (rows j,cols i)
  have hraw (i : S) : (fun j => R (i,j)) ∈
      Submodule.span ℝ (range (fun t j => R (rows t,j))) := by
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
      (hspan.symm ▸ row_mem_rowSpace R i)
    refine (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨c,?_⟩
    ext j
    have hh := congrArg (lp.evalCLM ℝ (fun _ : S => ℝ) 1 j) hc
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    simpa only [map_sum,map_smul,smul_eq_mul] using hh
  let b : Fin r → L1 S := fun s => ∑ t, P.adjugate t s •
    NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R
  have heq : P.det • R = ∑ s, outer (col (cols s) R) (b s) := by
    ext ij
    change P.det * R ij =
      (lp.evalCLM ℝ (fun _ : S×S => ℝ) 1 ij) (∑ s, outer (col (cols s) R) (b s))
    rw [map_sum]
    change P.det * R ij = ∑ s, R (ij.1,cols s) * b s ij.2
    have hh := pivot_reconstruction (fun i j => R (j,i)) rows cols hraw ij.2 ij.1
    change P.det * R ij = _ at hh
    rw [hh]
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    change _ = R (ij.1,cols s) *
      (lp.evalCLM ℝ (fun _ : S => ℝ) 1 ij.2)
        (∑ t, P.adjugate t s • NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R)
    simp only [map_sum,map_smul,smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    change R (rows t,ij.2) * (P.adjugate t s * R (ij.1,cols s)) =
      R (ij.1,cols s) * (P.adjugate t s * R (rows t,ij.2))
    ring
  have hs : P.det • R ∈ algebraicSpan := by
    rw [heq]
    exact Submodule.sum_mem _ (fun s _ => outer_mem _ _)
  exact (Submodule.smul_mem_iff _ hdet).mp hs

theorem mem_algebraicSpan_of_rankLE (r : ℕ) (R : MatrixL1 S S)
    (hR : RankLE r (coordinates (0,R))) : R ∈ algebraicSpan := by
  letI := finiteDimensional_rowSpace_rankLE r R hR
  exact mem_algebraicSpan_of_finiteDimensional R

theorem rankLE_of_finrank_rowSpace_le (r : ℕ) (R : MatrixL1 S S)
    [FiniteDimensional ℝ (rowSpace R)] (hdim : Module.finrank ℝ (rowSpace R) ≤ r) :
    RankLE r (coordinates (0,R)) := by
  classical
  intro rows cols
  by_contra hd
  let F : L1 S →ₗ[ℝ] (Fin (r+1) → ℝ) :=
    LinearMap.pi (fun j => (lp.evalCLM ℝ (fun _ : S => ℝ) 1 (cols j)).toLinearMap)
  have hli : LinearIndependent ℝ (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R) :=
    LinearIndependent.of_comp F (Matrix.linearIndependent_rows_of_det_ne_zero hd)
  let v : Fin (r+1) → rowSpace R := fun t =>
    ⟨NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R,row_mem_rowSpace R (rows t)⟩
  have hv : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (rowSpace R).subtype hli
  have hh := hv.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hh
  omega

theorem exists_rankLE_of_mem_algebraicSpan {R : MatrixL1 S S}
    (hR : R ∈ algebraicSpan) : ∃ r : ℕ, RankLE r (coordinates (0,R)) := by
  letI := finiteDimensional_rowSpace hR
  exact ⟨Module.finrank ℝ (rowSpace R),rankLE_of_finrank_rowSpace_le _ R le_rfl⟩

end ModNullUniversality.CompactTensor

end
end
-- END COMPLETE MODULE ModNullProof.WeakTensorRank

-- BEGIN COMPLETE MODULE ModNullProof.WeakTensorCharts
section
                                  
                                             

set_option autoImplicit false
noncomputable section
open Set Matrix
open scoped BigOperators

namespace ModNullUniversality.CompactTensor
open NoBorelUpperBoundFSigma.L1Coordinates
open NoBorelUpperBoundFSigma.SymmetricTensor
open NoBorelUpperBoundFSigma.TensorAlgebra

/-- The three reconstruction identities, without a lower determinant cutoff. -/
def ChartEquations (D : L1 S →L[ℝ] L1 S) (o : S) {r : ℕ}
    (rows qs : Fin r → S) (p : Space) : Prop :=
  (pivotD D rows qs p.2).det • p.2 = mapLeft D (liftNumerator D rows qs p.2) ∧
  transpose (liftNumerator D rows qs p.2) = liftNumerator D rows qs p.2 ∧
  (pivotD D rows qs p.2).det * p.1 = liftNumerator D rows qs p.2 (o,o)

/-- Every full-rank coordinate chart obeys the reconstruction identities. -/
def AllRankCharts (D : L1 S →L[ℝ] L1 S) (o : S) (p : Space) : Prop :=
  ∀ (r : ℕ) (rows qs : Fin r → S),
    RankLE r (coordinates p) → (pivotD D rows qs p.2).det ≠ 0 →
      ChartEquations D o rows qs p

/-- A nonzero D-pivot of the full coordinate rank selects an actual row basis. -/
theorem row_basis_of_rankLE_pivot (D : L1 S →L[ℝ] L1 S) {r : ℕ}
    (rows qs : Fin r → S) (R : MatrixL1 S S)
    (hR : RankLE r (coordinates (0,R))) (hdet : (pivotD D rows qs R).det ≠ 0) :
    LinearIndependent ℝ (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R) ∧
    Submodule.span ℝ (range (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R)) =
      rowSpace R := by
  classical
  let E : L1 S →ₗ[ℝ] (Fin r → ℝ) :=
    { toFun := fun v j => D v (qs j)
      map_add' := by intro v w; funext j; simp; rfl
      map_smul' := by intro c v; funext j; simp }
  have hpivot := Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hli : LinearIndependent ℝ
      (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R) :=
    LinearIndependent.of_comp E hpivot
  refine ⟨hli, ?_⟩
  letI := finiteDimensional_rowSpace_rankLE r R hR
  apply Submodule.eq_of_le_of_finrank_le
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,rfl⟩
    exact row_mem_rowSpace R (rows t)
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
    exact finrank_rowSpace_le_rankLE r R hR

/-- All full-rank charts of a genuine symmetric tensor image reconstruct it. -/
theorem chartEquations_of_mem_image (D : L1 S →L[ℝ] L1 S) (hD : Function.Injective D)
    (o : S) {p : Space} (hp : p ∈ imageSubmodule D o) {r : ℕ}
    (rows qs : Fin r → S) (hR : RankLE r (coordinates p))
    (hdet : (pivotD D rows qs p.2).det ≠ 0) : ChartEquations D o rows qs p := by
  classical
  obtain ⟨K,hK,rfl⟩ := hp
  let R := mapLeft D K
  let a : Fin r → L1 S := fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R
  have hKalg := symmetricSpan_le_algebraicSpan hK
  have hR0 : RankLE r (coordinates (0,R)) := hR
  have hspan := (row_basis_of_rankLE_pivot D rows qs R hR0 hdet).2
  have hcol (j : S) : NoBorelUpperBoundFSigma.L1Coordinates.col j K ∈
      Submodule.span ℝ (range a) := by
    change NoBorelUpperBoundFSigma.L1Coordinates.col j K ∈
      Submodule.span ℝ (range (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R))
    rw [hspan]
    have hc : NoBorelUpperBoundFSigma.L1Coordinates.col j K =
        NoBorelUpperBoundFSigma.L1Coordinates.row j K := by
      ext i
      exact symmetric_of_mem hK i j
    rw [hc]
    exact rowSpace_le_rowSpace_mapLeft D hD hKalg (row_mem_rowSpace K j)
  have hscaled : (pivotD D rows qs R).det • K = liftNumerator D rows qs R := by
    ext ij
    change (pivotD D rows qs R).det * K ij = liftNumerator D rows qs R ij
    rw [show ij = (ij.1,ij.2) from rfl,liftNumerator_apply]
    apply (reconstruction_from_image D a qs K hcol ij.1 ij.2).trans
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro s _
    change (a t ij.1) * ((pivotD D rows qs R).adjugate t s * R (qs s,ij.2)) = _
    change R (rows t,ij.1) * ((pivotD D rows qs R).adjugate t s * R (qs s,ij.2)) = _
    ring
  refine ⟨?_, ?_, ?_⟩
  · change (pivotD D rows qs R).det • R = mapLeft D (liftNumerator D rows qs R)
    rw [← hscaled,map_smul]
  · change transpose (liftNumerator D rows qs R) = liftNumerator D rows qs R
    rw [← hscaled,map_smul,transpose_eq_of_mem_symmetricSpan hK]
  · have h := congrArg (lp.evalCLM ℝ (fun _ : S×S => ℝ) 1 (o,o)) hscaled
    simpa only [map_smul,smul_eq_mul] using h

theorem allRankCharts_of_mem_image (D : L1 S →L[ℝ] L1 S) (hD : Function.Injective D)
    (o : S) {p : Space} (hp : p ∈ imageSubmodule D o) : AllRankCharts D o p :=
  fun _ rows qs hR hdet => chartEquations_of_mem_image D hD o hp rows qs hR hdet

/-- On finite-rank matrices the universal rank-chart equations suffice for membership. -/
theorem mem_image_of_finiteRank_allRankCharts (D : L1 S →L[ℝ] L1 S)
    (hD : Function.Injective D) (o : S) {p : Space}
    (hfinite : ∃ r, RankLE r (coordinates p)) (hall : AllRankCharts D o p) :
    p ∈ imageSubmodule D o := by
  classical
  obtain ⟨b,hb⟩ := hfinite
  have hb0 : RankLE b (coordinates (0,p.2)) := hb
  letI := finiteDimensional_rowSpace_rankLE b p.2 hb0
  obtain ⟨r,rows,hli,hspan⟩ := exists_row_basis_of_finiteDimensional p.2
  let a : Fin r → L1 S := fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) p.2
  have hliD : LinearIndependent ℝ (fun t i => D (a t) i) :=
    independent_coordinates (fun t => D (a t))
      (hli.map' D.toLinearMap (LinearMap.ker_eq_bot.mpr hD))
  obtain ⟨qs,hdet⟩ := exists_coordinate_pivot (fun t i => D (a t) i) hliD
  have hrank : Module.finrank ℝ (rowSpace p.2) ≤ r := by
    rw [← hspan,finrank_span_eq_card hli,Fintype.card_fin]
  have hR0 := rankLE_of_finrank_rowSpace_le r p.2 hrank
  have hR : RankLE r (coordinates p) := hR0
  have hd : (pivotD D rows qs p.2).det ≠ 0 := hdet
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt (abs_pos.mpr hd)
  apply imageChart_subset_image D o rows qs m
  exact ⟨hm.le,hall r rows qs hR hd⟩

/-- Finite coordinate rank plus universal chart equations characterize the tensor image. -/
theorem mem_image_iff_finiteRank_allRankCharts (D : L1 S →L[ℝ] L1 S)
    (hD : Function.Injective D) (o : S) (p : Space) :
    p ∈ imageSubmodule D o ↔
      (∃ r, RankLE r (coordinates p)) ∧ AllRankCharts D o p := by
  constructor
  · intro hp
    refine ⟨?_,allRankCharts_of_mem_image D hD o hp⟩
    obtain ⟨K,hK,hKp⟩ := hp
    have hRalg := mapLeft_mem_algebraicSpan D (symmetricSpan_le_algebraicSpan hK)
    obtain ⟨r,hr⟩ := exists_rankLE_of_mem_algebraicSpan hRalg
    refine ⟨r,?_⟩
    have hRp : mapLeft D K = p.2 := congrArg Prod.snd hKp
    rw [hRp] at hr
    exact hr
  · rintro ⟨hfinite,hall⟩
    exact mem_image_of_finiteRank_allRankCharts D hD o hfinite hall

end ModNullUniversality.CompactTensor

end
end
-- END COMPLETE MODULE ModNullProof.WeakTensorCharts

-- BEGIN COMPLETE MODULE ModNullProof.KSigmaComplexity
section
                                   

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace

namespace ModNullUniversality

variable {X : Type*} [TopologicalSpace X]

theorem isKSigma_of_isCompact {s : Set X} (hs : IsCompact s) : IsKSigma s :=
  ⟨fun _ => s,fun _ => hs,by ext x; simp⟩

theorem isKSigma_iUnion_nat {s : ℕ → Set X} (hs : ∀ n, IsKSigma (s n)) :
    IsKSigma (⋃ n, s n) := by
  classical
  choose C hC hseq using hs
  refine ⟨fun k => C k.unpair.1 k.unpair.2,fun k => hC _ _,?_⟩
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨n,hn⟩
    rw [hseq n] at hn
    obtain ⟨m,hm⟩ := mem_iUnion.mp hn
    exact ⟨Nat.pair n m,by simpa using hm⟩
  · rintro ⟨k,hk⟩
    refine ⟨k.unpair.1,?_⟩
    rw [hseq]
    exact mem_iUnion.mpr ⟨k.unpair.2,hk⟩

theorem isKSigma_iUnion {ι : Type*} [Countable ι] {s : ι → Set X}
    (hs : ∀ i, IsKSigma (s i)) : IsKSigma (⋃ i, s i) := by
  classical
  by_cases h : Nonempty ι
  · letI := h
    obtain ⟨e,he⟩ := exists_surjective_nat ι
    have hseq : (⋃ i, s i) = ⋃ n : ℕ, s (e n) := by
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨i,hi⟩
        obtain ⟨n,rfl⟩ := he i
        exact ⟨n,hi⟩
      · rintro ⟨n,hn⟩
        exact ⟨e n,hn⟩
    rw [hseq]
    exact isKSigma_iUnion_nat (fun n => hs (e n))
  · letI : IsEmpty ι := ⟨fun i => h ⟨i⟩⟩
    exact ⟨fun _ => ∅,fun _ => isCompact_empty,by ext x; simp⟩

theorem isKSigma_inter_isClosed {s t : Set X} (hs : IsKSigma s) (ht : IsClosed t) :
    IsKSigma (s ∩ t) := by
  obtain ⟨C,hC,rfl⟩ := hs
  refine ⟨fun n => C n ∩ t,fun n => (hC n).inter_right ht,?_⟩
  ext x
  simp only [mem_inter_iff,mem_iUnion]
  exact ⟨fun ⟨⟨i,hi⟩,ht⟩ => ⟨i,hi,ht⟩,
    fun ⟨i,hi,ht⟩ => ⟨⟨i,hi⟩,ht⟩⟩

end ModNullUniversality

end
end
-- END COMPLETE MODULE ModNullProof.KSigmaComplexity

-- BEGIN COMPLETE MODULE ModNullProof.TensorCompact
section
                                         
                                    
                                    

set_option autoImplicit false
noncomputable section
open Set Matrix
open scoped Topology BigOperators

namespace ModNullUniversality.CompactTensor
open NoBorelUpperBoundFSigma.L1Coordinates
open NoBorelUpperBoundFSigma.SymmetricTensor

theorem matrix_eq_iff_coordinates (A B : MatrixL1 S S) :
    A = B ↔ ∀ i j : S, A (i,j) = B (i,j) := by
  constructor
  · intro h i j
    exact congrArg (fun K : MatrixL1 S S => K (i,j)) h
  · intro h
    ext ij
    exact h ij.1 ij.2

theorem isGdelta_chartEquations (D : L1 S →L[ℝ] L1 S) (o : S) (M : ℝ)
    {r : ℕ} (rows qs : Fin r → S) :
    IsGδ {u : coordinateBall M | ChartEquations D o rows qs (ballSource M u)} := by
  have heq : {u : coordinateBall M | ChartEquations D o rows qs (ballSource M u)} =
      (⋂ i : S, ⋂ j : S, {u : coordinateBall M |
        (pivotD D rows qs (ballMatrix M u)).det * ballMatrix M u (i,j) =
          mapLeft D (liftNumerator D rows qs (ballMatrix M u)) (i,j)}) ∩
      (⋂ i : S, ⋂ j : S, {u : coordinateBall M |
        liftNumerator D rows qs (ballMatrix M u) (j,i) =
          liftNumerator D rows qs (ballMatrix M u) (i,j)}) ∩
      {u : coordinateBall M |
        (pivotD D rows qs (ballMatrix M u)).det * (ballSource M u).1 =
          liftNumerator D rows qs (ballMatrix M u) (o,o)} := by
    ext u
    simp only [mem_setOf_eq,ChartEquations,mem_inter_iff,mem_iInter,
      matrix_eq_iff_coordinates]
    exact and_assoc.symm
  rw [heq]
  apply IsGδ.inter
  · apply IsGδ.inter
    · exact IsGδ.iInter (fun i => IsGδ.iInter (fun j =>
        ((baireOne_pivotDet D M rows qs).mul (baireOne_matrix M (i,j))).isGdelta_eq
          (baireOne_mapLeft_lift D M rows qs i j)))
    · exact IsGδ.iInter (fun i => IsGδ.iInter (fun j =>
        (baireOne_lift D M rows qs j i).isGdelta_eq (baireOne_lift D M rows qs i j)))
  · exact ((baireOne_pivotDet D M rows qs).mul (baireOne_scalar M)).isGdelta_eq
      (baireOne_lift D M rows qs o o)

theorem isGdelta_allRankCharts (D : L1 S →L[ℝ] L1 S) (o : S) (M : ℝ) :
    IsGδ {u : coordinateBall M | AllRankCharts D o (ballSource M u)} := by
  have heq : {u : coordinateBall M | AllRankCharts D o (ballSource M u)} =
      ⋂ r : ℕ, ⋂ rows : Fin r → S, ⋂ qs : Fin r → S,
        ({u : coordinateBall M | ¬ RankLE r u.val} ∪
         {u : coordinateBall M | (pivotD D rows qs (ballMatrix M u)).det = 0} ∪
         {u : coordinateBall M | ChartEquations D o rows qs (ballSource M u)}) := by
    ext u
    simp only [mem_setOf_eq,AllRankCharts,coordinates_ballSource,mem_iInter,mem_union]
    change (∀ (r : ℕ) (rows qs : Fin r → S), RankLE r u.val →
      (pivotD D rows qs (ballMatrix M u)).det ≠ 0 →
        ChartEquations D o rows qs (ballSource M u)) ↔ _
    simp only [imp_iff_not_or,not_not,or_assoc]
  rw [heq]
  apply IsGδ.iInter
  intro r
  apply IsGδ.iInter
  intro rows
  apply IsGδ.iInter
  intro qs
  apply IsGδ.union
  · apply IsGδ.union
    · exact ((isClosed_rankLE r).preimage continuous_subtype_val).isOpen_compl.isGδ
    · exact (baireOne_pivotDet D M rows qs).isGdelta_zero
  · exact isGdelta_chartEquations D o M rows qs

/-- The countable union of bounded finite-rank coordinate sets. -/
def tensorEnvelope : Set Ambient :=
  ⋃ M : ℕ, ⋃ r : ℕ, coordinateBall M ∩ {u | RankLE r u}

/-- Every failed universal consistency test is removed, on every l1 ball. -/
def tensorObstruction (D : L1 S →L[ℝ] L1 S) (o : S) : Set Ambient :=
  ⋃ M : ℕ, Subtype.val '' {u : coordinateBall (M : ℝ) |
    ¬ AllRankCharts D o (ballSource M u)}

theorem isKSigma_tensorEnvelope : IsKSigma tensorEnvelope := by
  apply isKSigma_iUnion_nat
  intro M
  apply isKSigma_iUnion_nat
  intro r
  exact isKSigma_of_isCompact
    ((isCompact_coordinateBall M).inter_right (isClosed_rankLE r))

theorem isKSigma_tensorObstruction (D : L1 S →L[ℝ] L1 S) (o : S) :
    IsKSigma (tensorObstruction D o) := by
  apply isKSigma_iUnion_nat
  intro M
  exact isKSigma_subtype_image_of_isFSigma (isCompact_coordinateBall M)
    (isFSigma_compl_of_isGdelta (isGdelta_allRankCharts D o M))

theorem image_coordinates_eq_difference (D : L1 S →L[ℝ] L1 S)
    (hD : Function.Injective D) (o : S) :
    coordinates '' (imageSubmodule D o : Set Space) = tensorEnvelope \ tensorObstruction D o := by
  ext u
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨hfinite,hall⟩ := (mem_image_iff_finiteRank_allRankCharts D hD o p).mp hp
    obtain ⟨M,hM⟩ := exists_coordinateBall p
    obtain ⟨r,hr⟩ := hfinite
    refine ⟨mem_iUnion.mpr ⟨M,mem_iUnion.mpr ⟨r,hM,hr⟩⟩,?_⟩
    rintro hbad
    obtain ⟨N,v,hv,hvu⟩ := mem_iUnion.mp hbad
    have hpv : ballSource N v = p :=
      coordinates_injective ((coordinates_ballSource N v).trans hvu)
    exact hv (hpv.symm ▸ hall)
  · rintro ⟨henv,hnot⟩
    obtain ⟨M,henv⟩ := mem_iUnion.mp henv
    obtain ⟨r,hM,hr⟩ := mem_iUnion.mp henv
    let v : coordinateBall (M : ℝ) := ⟨u,hM⟩
    have hall : AllRankCharts D o (ballSource M v) := by
      by_contra hbad
      apply hnot
      exact mem_iUnion.mpr ⟨M,v,hbad,rfl⟩
    refine ⟨ballSource M v,?_,coordinates_ballSource M v⟩
    apply (mem_image_iff_finiteRank_allRankCharts D hD o _).mpr
    refine ⟨⟨r,?_⟩,hall⟩
    rw [coordinates_ballSource]
    exact hr

/-- Actual compact coordinate complexity of every scalar-tagged tensor subgroup. -/
theorem image_coordinates_difference_ksigma (D : L1 S →L[ℝ] L1 S)
    (hD : Function.Injective D) (o : S) :
    ∃ A B : Set Ambient, IsKSigma A ∧ IsKSigma B ∧
      coordinates '' (imageSubmodule D o : Set Space) = A \ B :=
  ⟨tensorEnvelope,tensorObstruction D o,isKSigma_tensorEnvelope,
    isKSigma_tensorObstruction D o,image_coordinates_eq_difference D hD o⟩

end ModNullUniversality.CompactTensor

end
end
-- END COMPLETE MODULE ModNullProof.TensorCompact

-- BEGIN COMPLETE MODULE ModNullProof.CompactFamily
section
                                    
                                 

set_option autoImplicit false
noncomputable section

namespace ModNullUniversality.CompactTensor

def compactFamily (T : WF) : Subgroup compactGroup.Carrier :=
  compactSubgroup (tensorSubspace T)

theorem tensorSubspace_coordinate_complexity (T : WF) :
    ∃ A B : Set Ambient, IsKSigma A ∧ IsKSigma B ∧
      coordinates '' (tensorSubspace T : Set Space) = A \ B :=
  image_coordinates_difference_ksigma (treeOperator T) (treeOperator_injective T) []

theorem compactFamily_lowComplexity : LowComplexityFamily compactGroup compactFamily :=
  compactSubgroup_lowComplexity tensorSubspace tensorSubspace_coordinate_complexity

theorem compactFamily_measurable (T : WF) :
    MeasurableSet (compactFamily T : Set compactGroup.Carrier) := by
  change MeasurableSet (compactSubgroup (tensorSubspace T) : Set Target)
  exact differenceFSigma_measurableSet
    (compactSubgroup_differenceFSigma (tensorSubspace T) (tensorSubspace_coordinate_complexity T))

theorem compactFamily_unbounded (F : StandardBorelEquivalence) :
    ∃ T : WF, ¬ BorelReducible (CosetRelation compactGroup (compactFamily T)) F.rel :=
  compact_family_unbounded F

end ModNullUniversality.CompactTensor

end
end
-- END COMPLETE MODULE ModNullProof.CompactFamily

-- BEGIN COMPLETE MODULE ModNullProof.AEPowerRealCodes
section
                                                     
                                                     
                                          
                                                               
                                                             
                                                           
                                            

/-!
An explicit Borel coding of measurable real functions, using rapidly convergent
approximations from a fixed countable dense subset of L¹.  Codes themselves are
Baire space; every code has a jointly Borel interpretation (by pointwise limsup).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ModNullUniversality.AEPower

abbrev Code := ℕ → ℕ

local instance : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

section RealCodes

variable {T : Type*} [MeasurableSpace T] [MeasurableSpace.CountablyGenerated T]
variable (μ : Measure T) [IsFiniteMeasure μ]

/-- A fixed dense sequence in real L¹. -/
noncomputable def centers : ℕ → T →₁[μ] ℝ :=
  TopologicalSpace.denseSeq (T →₁[μ] ℝ)

theorem dense_centers : DenseRange (centers μ) :=
  TopologicalSpace.denseRange_denseSeq _

theorem measurable_centers :
    Measurable (fun p : ℕ × T => centers μ p.1 p.2) :=
  measurable_from_prod_countable_right (fun j => L1.measurable_coeFn (centers μ j))

/-- All Baire codes are interpreted, whether or not their approximants converge. -/
noncomputable def realDecode (s : Code) (t : T) : ℝ :=
  (limsup (fun n => (centers μ (s n) t : EReal)) atTop).toReal

theorem measurable_realDecode :
    Measurable (fun p : Code × T => realDecode μ p.1 p.2) := by
  apply Measurable.ereal_toReal
  apply Measurable.limsup
  intro n
  have h : Measurable (fun p : Code × T => centers μ (p.1 n) p.2) :=
    (measurable_centers μ).comp (show Measurable (fun p : Code × T => (p.1 n, p.2)) by
      exact ((measurable_pi_apply n).comp measurable_fst).prodMk measurable_snd)
  simpa only [Function.comp_def] using
    measurable_coe_real_ereal.comp h

/-- Summable L¹ errors force the Borel interpretation to recover the given function a.e. -/
theorem realDecode_eq_ae_of_summable {s : Code} {a : T → ℝ} (ha : Measurable a)
    (hs : (∑' n, ∫⁻ t, edist (centers μ (s n) t) (a t) ∂μ) ≠ ∞) :
    realDecode μ s =ᵐ[μ] a := by
  have hm (n : ℕ) : Measurable (fun t => edist (centers μ (s n) t) (a t)) :=
    (L1.measurable_coeFn _).edist ha
  have ht : (∫⁻ t, ∑' n, edist (centers μ (s n) t) (a t) ∂μ) ≠ ∞ := by
    rw [lintegral_tsum (fun n => (hm n).aemeasurable)]
    exact hs
  filter_upwards [ae_lt_top (Measurable.tsum hm) ht] with t ht
  have hzero := ENNReal.tendsto_atTop_zero_of_tsum_ne_top ht.ne
  have hdist : Tendsto (fun n => dist (centers μ (s n) t) (a t)) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, ← dist_edist] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hzero
  have hconv : Tendsto (fun n => centers μ (s n) t) atTop (𝓝 (a t)) :=
    tendsto_iff_dist_tendsto_zero.mpr hdist
  have he := (continuous_coe_real_ereal.tendsto (a t)).comp hconv
  change Tendsto (fun n => (centers μ (s n) t : EReal)) atTop (𝓝 (a t : EReal)) at he
  rw [realDecode, he.limsup_eq, EReal.toReal_coe]

/-- The error used in the least-index coding procedure. -/
noncomputable def approxError {X : Type*} (a : X × T → ℝ) (x : X) (j : ℕ) : ℝ≥0∞ :=
  ∫⁻ t, edist (centers μ j t) (a (x, t)) ∂μ

theorem measurable_approxError {X : Type*} [MeasurableSpace X]
    {a : X × T → ℝ} (ha : Measurable a) (j : ℕ) :
    Measurable (fun x => approxError μ a x j) := by
  exact (((L1.measurable_coeFn (centers μ j)).comp measurable_snd).edist ha).lintegral_prod_right

theorem exists_approxError_lt {X : Type*} {a : X × T → ℝ} (x : X)
    (ha : Integrable (fun t => a (x, t)) μ) (n : ℕ) :
    ∃ j, approxError μ a x j < (2⁻¹ : ℝ≥0∞) ^ n := by
  let b := ha.toL1 (fun t => a (x, t))
  obtain ⟨j, hj⟩ := (dense_centers μ).exists_dist_lt b
    (show 0 < (2⁻¹ : ℝ) ^ n by positivity)
  refine ⟨j, ?_⟩
  have he : approxError μ a x j = edist (centers μ j) b := by
    rw [L1.edist_def]
    apply lintegral_congr_ae
    filter_upwards [ha.coeFn_toL1] with t ht
    rw [ht]
  rw [he, edist_dist, dist_comm]
  have hε : ENNReal.ofReal ((2⁻¹ : ℝ) ^ n) = (2⁻¹ : ℝ≥0∞) ^ n := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  rw [← hε]
  exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr hj

/-- Measurable rapidly converging codes for a jointly Borel integrable family. -/
theorem exists_measurable_realCode {X : Type*} [MeasurableSpace X]
    {a : X × T → ℝ} (ha : Measurable a)
    (hint : ∀ x, Integrable (fun t => a (x, t)) μ) :
    ∃ c : X → Code, Measurable c ∧
      ∀ x, realDecode μ (c x) =ᵐ[μ] (fun t => a (x, t)) := by
  classical
  have hex (x : X) (n : ℕ) : ∃ j, approxError μ a x j < (2⁻¹ : ℝ≥0∞) ^ n :=
    exists_approxError_lt μ x (hint x) n
  let c : X → Code := fun x n => Nat.find (hex x n)
  refine ⟨c, measurable_pi_lambda _ (fun n => ?_), fun x => ?_⟩
  · exact measurable_find (fun x => hex x n) (fun j =>
      measurableSet_lt (measurable_approxError μ ha j) measurable_const)
  · apply realDecode_eq_ae_of_summable μ
      (ha.comp (measurable_const.prodMk measurable_id))
    apply ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    calc
      (∑' n, ∫⁻ t, edist (centers μ (c x n) t) (a (x, t)) ∂μ) ≤
          ∑' n, (2⁻¹ : ℝ≥0∞) ^ n :=
        ENNReal.tsum_le_tsum (fun n => (Nat.find_spec (hex x n)).le)
      _ = 2 := ENNReal.tsum_geometric_two

end RealCodes

end ModNullUniversality.AEPower

end
-- END COMPLETE MODULE ModNullProof.AEPowerRealCodes

-- BEGIN COMPLETE MODULE ModNullProof.AEPowerBorel
section
                                    
                                          
                                         

/-!
An almost-everywhere power of a Borel equivalence relation, realized on Baire
space by explicit real-function codes.  The construction includes the Borel
parameter coding theorem, with no selection or representation assumptions.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ModNullUniversality.AEPower

section Target

variable (Y : Type*) [MeasurableSpace Y] [StandardBorelSpace Y]

/-- A bounded real Borel embedding of any standard Borel space. -/
noncomputable def boundedEmbedding (y : Y) : ℝ :=
  Real.arctan (embeddingReal Y y)

theorem measurableEmbedding_boundedEmbedding : MeasurableEmbedding (boundedEmbedding Y) :=
  (Real.continuous_arctan.measurableEmbedding Real.arctan_injective).comp
    (measurableEmbedding_embeddingReal Y)

theorem norm_boundedEmbedding_le (y : Y) : ‖boundedEmbedding Y y‖ ≤ Real.pi / 2 := by
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩

variable [Nonempty Y]

/-- A total Borel inverse, assigned an arbitrary value outside the embedded range. -/
noncomputable def boundedInverse : ℝ → Y :=
  (measurableEmbedding_boundedEmbedding Y).invFun

theorem measurable_boundedInverse : Measurable (boundedInverse Y) :=
  (measurableEmbedding_boundedEmbedding Y).measurable_invFun

@[simp] theorem boundedInverse_boundedEmbedding (y : Y) :
    boundedInverse Y (boundedEmbedding Y y) = y :=
  (measurableEmbedding_boundedEmbedding Y).leftInverse_invFun y

variable {T : Type*} [MeasurableSpace T] [MeasurableSpace.CountablyGenerated T]
variable (μ : Measure T) [IsFiniteMeasure μ]

/-- The jointly Borel interpretation of Baire codes in the target space. -/
noncomputable def decode (s : Code) (t : T) : Y :=
  boundedInverse Y (realDecode μ s t)

theorem measurable_decode : Measurable (fun p : Code × T => decode Y μ p.1 p.2) :=
  (measurable_boundedInverse Y).comp (measurable_realDecode μ)

/-- Every jointly Borel family has measurable codes recovering all its sections a.e. -/
theorem exists_measurable_code {X : Type*} [MeasurableSpace X]
    {a : X × T → Y} (ha : Measurable a) :
    ∃ c : X → Code, Measurable c ∧
      ∀ x, decode Y μ (c x) =ᵐ[μ] (fun t => a (x, t)) := by
  have hb : Measurable (fun p => boundedEmbedding Y (a p)) :=
    (measurableEmbedding_boundedEmbedding Y).measurable.comp ha
  have hint (x : X) : Integrable (fun t => boundedEmbedding Y (a (x, t))) μ := by
    exact (integrable_const (Real.pi / 2)).mono'
      ((hb.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (Eventually.of_forall fun t => norm_boundedEmbedding_le Y _)
  obtain ⟨c, hc, hcx⟩ := exists_measurable_realCode μ hb hint
  refine ⟨c, hc, fun x => ?_⟩
  filter_upwards [hcx x] with t ht
  simp only [decode, ht, boundedInverse_boundedEmbedding]

end Target

section Relation

variable {T : Type} [MeasurableSpace T] [MeasurableSpace.CountablyGenerated T]
variable (μ : Measure T) [IsFiniteMeasure μ]
variable (F : StandardBorelEquivalence) [Nonempty F.Carrier]

/-- Almost-everywhere pointwise equivalence, on the fixed Baire coding space. -/
noncomputable def powerRelation (s r : Code) : Prop :=
  ∀ᵐ t ∂μ, F.rel (decode F.Carrier μ s t) (decode F.Carrier μ r t)

theorem powerRelation_equivalence : Equivalence (powerRelation μ F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    exact Eventually.of_forall fun t => F.equivalence.refl _
  · intro s r h
    exact h.mono fun t ht => F.equivalence.symm ht
  · intro s r u hsr hru
    filter_upwards [hsr, hru] with t hsr hru
    exact F.equivalence.trans hsr hru

theorem measurableSet_powerRelation :
    MeasurableSet {p : Code × Code | powerRelation μ F p.1 p.2} := by
  have hp₁ : Measurable (fun p : (Code × Code) × T => (p.1.1, p.2)) :=
    ((measurable_fst : Measurable (Prod.fst : Code × Code → Code)).comp
      measurable_fst).prodMk measurable_snd
  have hp₂ : Measurable (fun p : (Code × Code) × T => (p.1.2, p.2)) :=
    ((measurable_snd : Measurable (Prod.snd : Code × Code → Code)).comp
      measurable_fst).prodMk measurable_snd
  have hm₁ : Measurable (fun p : (Code × Code) × T => decode F.Carrier μ p.1.1 p.2) := by
    simpa only [Function.comp_def] using (measurable_decode F.Carrier μ).comp hp₁
  have hm₂ : Measurable (fun p : (Code × Code) × T => decode F.Carrier μ p.1.2 p.2) := by
    simpa only [Function.comp_def] using (measurable_decode F.Carrier μ).comp hp₂
  have hs : MeasurableSet {p : (Code × Code) × T |
      ¬F.rel (decode F.Carrier μ p.1.1 p.2) (decode F.Carrier μ p.1.2 p.2)} :=
    (F.measurable_graph.preimage (hm₁.prodMk hm₂)).compl
  have hμ := measurable_measure_prodMk_left (ν := μ) hs
  simpa only [powerRelation, ae_iff] using measurableSet_eq_fun hμ measurable_const

/-- The fixed standard Borel target for the almost-everywhere power. -/
noncomputable def power : StandardBorelEquivalence where
  Carrier := Code
  rel := powerRelation μ F
  equivalence := powerRelation_equivalence μ F
  measurable_graph := measurableSet_powerRelation μ F

end Relation

end ModNullUniversality.AEPower

end
-- END COMPLETE MODULE ModNullProof.AEPowerBorel

-- BEGIN COMPLETE MODULE ModNullProof.HaarAmplification
section
                                
                                             
                                       

/-!
The Haar amplification lemma.  A reduction defined on a conull set is encoded
by the whole family of its left translates.  Right translations quasi-preserve
Haar measure, so for each pair of points the coded functions compare exactly
as the original coset relation, almost everywhere.
-/

open MeasureTheory Filter Topology Set

namespace ModNullUniversality

theorem haar_amplification_proved
    (K : CompactMetrizableHaarGroup) (F : StandardBorelEquivalence)
    (hF : Nonempty F.Carrier) :
    ∃ Q : StandardBorelEquivalence,
      ∀ H : Subgroup K.Carrier, MeasurableSet (H : Set K.Carrier) →
        ∀ C : Set K.Carrier, MeasurableSet C → K.haar C = 1 →
          BorelReducible
            (fun x y : C => CosetRelation K H x.val y.val) F.rel →
          BorelReducible (CosetRelation K H) Q.rel := by
  letI : MetricSpace K.Carrier := TopologicalSpace.metrizableSpaceMetric K.Carrier
  letI : SecondCountableTopology K.Carrier := inferInstance
  letI : Nonempty F.Carrier := hF
  refine ⟨AEPower.power K.haar F, ?_⟩
  intro H _ C hCm hC hred
  obtain ⟨f, hf, hfred⟩ := hred
  obtain ⟨g, hg, hgf⟩ := (MeasurableEmbedding.subtype_coe hCm).exists_measurable_extend
    hf (fun _ => hF)
  have hext (z : K.Carrier) (hz : z ∈ C) : g z = f ⟨z, hz⟩ :=
    congrFun hgf ⟨z, hz⟩
  let a : K.Carrier × K.Carrier → F.Carrier := fun p => g (p.2 * p.1)
  have ha : Measurable a := hg.comp (measurable_snd.mul measurable_fst)
  obtain ⟨c, hc, hcode⟩ := AEPower.exists_measurable_code F.Carrier K.haar ha
  refine ⟨c, hc, fun x y => ?_⟩
  change CosetRelation K H x y ↔
    ∀ᵐ t ∂K.haar, F.rel (AEPower.decode F.Carrier K.haar (c x) t)
      (AEPower.decode F.Carrier K.haar (c y) t)
  have hmem : ∀ᵐ t ∂K.haar, t ∈ C :=
    (ae_mem_iff_measure_eq hCm.nullMeasurableSet).mpr (by simpa using hC)
  have hxmem : ∀ᵐ t ∂K.haar, t * x ∈ C :=
    (quasiMeasurePreserving_mul_right K.haar x).ae hmem
  have hymem : ∀ᵐ t ∂K.haar, t * y ∈ C :=
    (quasiMeasurePreserving_mul_right K.haar y).ae hmem
  have hcompare : ∀ᵐ t ∂K.haar,
      F.rel (AEPower.decode F.Carrier K.haar (c x) t)
        (AEPower.decode F.Carrier K.haar (c y) t) ↔ CosetRelation K H x y := by
    filter_upwards [hcode x, hcode y, hxmem, hymem] with t hx hy htx hty
    rw [hx, hy]
    change F.rel (g (t * x)) (g (t * y)) ↔ CosetRelation K H x y
    rw [hext (t * x) htx, hext (t * y) hty]
    have hcos : CosetRelation K H (t * x) (t * y) ↔ CosetRelation K H x y := by
      simp [CosetRelation, mul_inv_rev, mul_assoc]
    exact (hfred ⟨t * x, htx⟩ ⟨t * y, hty⟩).symm.trans hcos
  constructor
  · intro hxy
    exact hcompare.mono fun t ht => ht.mpr hxy
  · intro hxy
    have hconst : ∀ᵐ _t ∂K.haar, CosetRelation K H x y := by
      filter_upwards [hxy, hcompare] with t ht hc
      exact hc.mp ht
    exact hconst.exists.choose_spec

end ModNullUniversality

end
-- END COMPLETE MODULE ModNullProof.HaarAmplification

-- BEGIN COMPLETE MODULE Solutions.HaarAmplification
section
                                     

set_option autoImplicit false

namespace ModNullUniversality

/-- Uniform Haar amplification: a fixed Borel target absorbs every conull reduction. -/
theorem haar_amplification
    (K : CompactMetrizableHaarGroup) (F : StandardBorelEquivalence)
    (hF : Nonempty F.Carrier) :
    ∃ Q : StandardBorelEquivalence,
      ∀ H : Subgroup K.Carrier, MeasurableSet (H : Set K.Carrier) →
        ∀ C : Set K.Carrier, MeasurableSet C → K.haar C = 1 →
          BorelReducible
            (fun x y : C => CosetRelation K H x.val y.val) F.rel →
          BorelReducible (CosetRelation K H) Q.rel :=
  haar_amplification_proved K F hF

end ModNullUniversality

end
-- END COMPLETE MODULE Solutions.HaarAmplification

-- BEGIN COMPLETE MODULE ModNullProof.ConullAssembly
section
                                  

set_option autoImplicit false
noncomputable section
open Set MeasureTheory

namespace ModNullUniversality

/-- Uniform amplification preserves unboundedness on every conull restriction. -/
theorem conull_unbounded_of_unbounded
    (K : CompactMetrizableHaarGroup) (H : WF → Subgroup K.Carrier)
    (hH : ∀ T, MeasurableSet (H T : Set K.Carrier))
    (hunbounded : ∀ F : StandardBorelEquivalence,
      ∃ T : WF, ¬ BorelReducible (CosetRelation K (H T)) F.rel) :
    ∀ F : StandardBorelEquivalence,
      ∃ T : WF, ∀ C : Set K.Carrier, MeasurableSet C → K.haar C = 1 →
        ¬ BorelReducible (fun x y : C => CosetRelation K (H T) x.val y.val) F.rel := by
  classical
  intro F
  by_cases hF : Nonempty F.Carrier
  · obtain ⟨Q,hQ⟩ := haar_amplification K F hF
    obtain ⟨T,hT⟩ := hunbounded Q
    refine ⟨T,fun C hC hμ hred => ?_⟩
    exact hT (hQ (H T) (hH T) C hC hμ hred)
  · obtain ⟨T,_⟩ := hunbounded F
    refine ⟨T,fun C _ hμ hred => ?_⟩
    have hne : C.Nonempty := by
      by_contra hn
      have hzero : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      simpa only [hzero,measure_empty,zero_ne_one] using hμ
    obtain ⟨x,hx⟩ := hne
    obtain ⟨f,_,_⟩ := hred
    exact hF ⟨f ⟨x,hx⟩⟩

end ModNullUniversality

end
end
-- END COMPLETE MODULE ModNullProof.ConullAssembly

-- BEGIN COMPLETE MODULE Solutions.Main
section
                                 
                                  

set_option autoImplicit false
noncomputable section

namespace ModNullUniversality

/-- Theorem 1.1: the fixed compact Haar family is unbounded on all conull sets. -/
theorem theorem1_1 :
    ∃ K : CompactMetrizableHaarGroup, IsAbelian K ∧
      ∃ H : WF → Subgroup K.Carrier, LowComplexityFamily K H ∧
        ∀ F : StandardBorelEquivalence, ∃ T : WF,
          ∀ C : Set K.Carrier, MeasurableSet C → K.haar C = 1 →
            ¬ BorelReducible
              (fun x y : C => CosetRelation K (H T) x.val y.val) F.rel := by
  refine ⟨CompactTensor.compactGroup,CompactTensor.compactGroup_abelian,
    CompactTensor.compactFamily,CompactTensor.compactFamily_lowComplexity,?_⟩
  exact conull_unbounded_of_unbounded CompactTensor.compactGroup CompactTensor.compactFamily
    CompactTensor.compactFamily_measurable CompactTensor.compactFamily_unbounded

end ModNullUniversality

end
end
-- END COMPLETE MODULE Solutions.Main

set_option autoImplicit false

theorem solution :
    ∃ K : ModNullUniversality.CompactMetrizableHaarGroup,
      ModNullUniversality.IsAbelian K ∧
      ∃ H : ModNullUniversality.WF → Subgroup K.Carrier,
        ModNullUniversality.LowComplexityFamily K H ∧
        ∀ F : ModNullUniversality.StandardBorelEquivalence,
          ∃ T : ModNullUniversality.WF,
            ∀ C : Set K.Carrier, MeasurableSet C → K.haar C = 1 →
              ¬ ModNullUniversality.BorelReducible
                (fun x y : C => ModNullUniversality.CosetRelation K (H T) x.val y.val)
                F.rel := by
  first
  | exact @ModNullUniversality.theorem1_1
  | apply @ModNullUniversality.theorem1_1 <;> assumption

#print axioms solution
