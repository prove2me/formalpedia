-- Prove2me | solution 1 for ModNullUniversality.haar_amplification
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-11-09T09:43:51.22168+00:00
-- url     : https://prove2.me/submissions/0308963b-896a-406a-8ca5-7d4a80f4b11b

import Definitions.Def_ModNullCompact20261109
import Definitions.Def_ModNullCore20261109
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure

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

set_option autoImplicit false

theorem solution
    (K : ModNullUniversality.CompactMetrizableHaarGroup)
    (F : ModNullUniversality.StandardBorelEquivalence)
    (hF : Nonempty F.Carrier) :
    ∃ Q : ModNullUniversality.StandardBorelEquivalence,
      ∀ H : Subgroup K.Carrier, MeasurableSet (H : Set K.Carrier) →
        ∀ C : Set K.Carrier, MeasurableSet C → K.haar C = 1 →
          ModNullUniversality.BorelReducible
            (fun x y : C => ModNullUniversality.CosetRelation K H x.val y.val) F.rel →
          ModNullUniversality.BorelReducible (ModNullUniversality.CosetRelation K H) Q.rel := by
  first
  | exact @ModNullUniversality.haar_amplification
  | apply @ModNullUniversality.haar_amplification <;> assumption

#print axioms solution
