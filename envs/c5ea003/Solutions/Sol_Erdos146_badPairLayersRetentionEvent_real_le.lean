-- Prove2me | solution 1 for Erdos146.badPairLayersRetentionEvent_real_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:32:57.551183+00:00
-- url     : https://prove2.me/submissions/1fa986c6-0aaf-4dfd-b86e-5b6e952d5168

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.MeasureTheory.Measure.Real
import Theorems.Thm_Erdos146_hammingRetentionMeasure_real_contains_finset

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem binomial_probability_term_le_one
    (trialCount successCount : ℕ) (probability : ℝ)
    (hcount : successCount ≤ trialCount)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1) :
    (trialCount.choose successCount : ℝ) *
        probability ^ successCount *
        (1 - probability) ^ (trialCount - successCount) ≤ 1 := by
  have hcomplement : 0 ≤ 1 - probability :=
    sub_nonneg.mpr hprobability_one
  have hsum :
      (∑ count ∈ Finset.range (trialCount + 1),
        probability ^ count *
          (1 - probability) ^ (trialCount - count) *
          (trialCount.choose count : ℝ)) = 1 := by
    calc
      (∑ count ∈ Finset.range (trialCount + 1),
          probability ^ count *
            (1 - probability) ^ (trialCount - count) *
            (trialCount.choose count : ℝ)) =
          (probability + (1 - probability)) ^ trialCount :=
        (add_pow probability (1 - probability) trialCount).symm
      _ = 1 := by
        rw [show probability + (1 - probability) = 1 by ring]
        simp
  have hterm := Finset.single_le_sum
    (s := Finset.range (trialCount + 1))
    (f := fun count : ℕ =>
      probability ^ count *
        (1 - probability) ^ (trialCount - count) *
        (trialCount.choose count : ℝ))
    (fun count _ => by positivity)
    (show successCount ∈ Finset.range (trialCount + 1) by
      simp; omega)
  rw [hsum] at hterm
  nlinarith

theorem log_choose_le_binary_entropy
    (trialCount successCount : ℕ)
    (hcount : successCount ≤ trialCount) :
    Real.log (trialCount.choose successCount : ℝ) ≤
      (trialCount : ℝ) *
        Real.binEntropy ((successCount : ℝ) / (trialCount : ℝ)) := by
  by_cases hzero : successCount = 0
  · subst successCount
    simp
  by_cases hfull : successCount = trialCount
  · subst successCount
    by_cases htrials : trialCount = 0
    · simp [htrials]
    · have htrials_real : (trialCount : ℝ) ≠ 0 := by
        exact_mod_cast htrials
      simp [htrials_real]
  have hsuccess : 0 < successCount := Nat.pos_of_ne_zero hzero
  have hstrict : successCount < trialCount :=
    lt_of_le_of_ne hcount hfull
  have htrials : 0 < trialCount :=
    lt_of_lt_of_le hsuccess hcount
  let probability : ℝ :=
    (successCount : ℝ) / (trialCount : ℝ)
  have hprobability_pos : 0 < probability := by
    dsimp [probability]
    positivity
  have hprobability_lt_one : probability < 1 := by
    dsimp [probability]
    apply (div_lt_one (by exact_mod_cast htrials)).mpr
    exact_mod_cast hstrict
  have hcomplement : 0 < 1 - probability :=
    sub_pos.mpr hprobability_lt_one
  have hchoose : 0 < (trialCount.choose successCount : ℝ) := by
    exact_mod_cast Nat.choose_pos hcount
  have hmass := binomial_probability_term_le_one
    trialCount successCount probability hcount
    hprobability_pos.le hprobability_lt_one.le
  have hproduct :
      0 < (trialCount.choose successCount : ℝ) *
        probability ^ successCount *
        (1 - probability) ^ (trialCount - successCount) := by
    positivity
  have hlogmass := Real.log_le_log hproduct hmass
  simp only [Real.log_one] at hlogmass
  rw [Real.log_mul
      (mul_pos hchoose (pow_pos hprobability_pos _)).ne'
      (pow_pos hcomplement _).ne',
    Real.log_mul hchoose.ne' (pow_pos hprobability_pos _).ne',
    Real.log_pow, Real.log_pow] at hlogmass
  have htrials_real : (trialCount : ℝ) ≠ 0 := by
    exact_mod_cast htrials.ne'
  have hentropy :
      (trialCount : ℝ) * Real.binEntropy probability =
        -(successCount : ℝ) * Real.log probability -
          ((trialCount - successCount : ℕ) : ℝ) *
            Real.log (1 - probability) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv, Nat.cast_sub hcount]
    dsimp [probability]
    field_simp [htrials_real]
    ring
  change Real.log (trialCount.choose successCount : ℝ) ≤
    (trialCount : ℝ) * Real.binEntropy probability
  rw [hentropy]
  linarith

theorem choose_le_exp_binary_entropy
    (trialCount successCount : ℕ)
    (hcount : successCount ≤ trialCount) :
    (trialCount.choose successCount : ℝ) ≤
      Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy ((successCount : ℝ) / (trialCount : ℝ))) := by
  have hchoose : 0 < (trialCount.choose successCount : ℝ) := by
    exact_mod_cast Nat.choose_pos hcount
  exact (Real.log_le_iff_le_exp hchoose).mp
    (log_choose_le_binary_entropy trialCount successCount hcount)

theorem choose_product_le_exp_binary_entropy
    {ι : Type*} [Fintype ι]
    (population success : ι → ℕ)
    (hcount : ∀ index, success index ≤ population index) :
    (∏ index : ι,
      (population index).choose (success index) : ℝ) ≤
      Real.exp
        (∑ index : ι,
          (population index : ℝ) *
            Real.binEntropy
              ((success index : ℝ) / (population index : ℝ))) := by
  calc
    (∏ index : ι,
        (population index).choose (success index) : ℝ) ≤
      ∏ index : ι,
        Real.exp
          ((population index : ℝ) *
            Real.binEntropy
              ((success index : ℝ) / (population index : ℝ))) := by
        apply Finset.prod_le_prod
        · intro index _
          positivity
        · intro index _
          exact choose_le_exp_binary_entropy
            (population index) (success index) (hcount index)
    _ = Real.exp
        (∑ index : ι,
          (population index : ℝ) *
            Real.binEntropy
              ((success index : ℝ) / (population index : ℝ))) := by
      rw [Real.exp_sum]

theorem booleanWordsOfWeight_card
    (ι : Type*) [Fintype ι] (weight : ℕ) :
    (booleanWordsOfWeight ι weight).card =
      (Fintype.card ι).choose weight := by
  calc
    (booleanWordsOfWeight ι weight).card =
        Fintype.card ↥(booleanWordsOfWeight ι weight) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        ↥((Finset.univ : Finset ι).powersetCard weight) :=
      Fintype.card_congr (booleanWordsOfWeightEquiv ι weight)
    _ = ((Finset.univ : Finset ι).powersetCard weight).card :=
      Fintype.card_coe _
    _ = (Fintype.card ι).choose weight := by
      simp

theorem classifiedBooleanWords_card
    {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (classify : ι → γ) (counts : γ → ℕ) :
    (classifiedBooleanWords classify counts).card =
      ∏ group : γ,
        (Fintype.card (ClassificationFiber classify group)).choose
          (counts group) := by
  calc
    (classifiedBooleanWords classify counts).card =
        Fintype.card ↥(classifiedBooleanWords classify counts) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        (∀ group : γ,
          ↥(booleanWordsOfWeight
            (ClassificationFiber classify group) (counts group))) :=
      Fintype.card_congr (classifiedBooleanWordsEquiv classify counts)
    _ = ∏ group : γ,
          Fintype.card
            ↥(booleanWordsOfWeight
              (ClassificationFiber classify group) (counts group)) := by
      rw [Fintype.card_pi]
    _ = ∏ group : γ,
          (Fintype.card (ClassificationFiber classify group)).choose
            (counts group) := by
      apply Finset.prod_congr rfl
      intro group _
      rw [Fintype.card_coe,
        booleanWordsOfWeight_card]

theorem pairTypeCountProfile_card (parentCount dimension : ℕ) :
    Fintype.card (PairTypeCountProfile parentCount dimension) =
      (parentCount.choose 2 + 1) ^ (3 * dimension) := by
  simp [PairTypeCountProfile, pow_mul, Nat.mul_comm]

theorem pairCoordinateClassificationFiber_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (bitType : PairBitType) (coordinate : Fin dimension) :
    Fintype.card
      (ClassificationFiber
        (pairCoordinateClassification parents) (bitType, coordinate)) =
      (pairTypeGroup parents coordinate bitType).card := by
  calc
    Fintype.card
        (ClassificationFiber
          (pairCoordinateClassification parents) (bitType, coordinate)) =
        Fintype.card ↥(pairTypeGroup parents coordinate bitType) :=
      Fintype.card_congr
        (pairCoordinateClassificationFiberEquiv parents bitType coordinate)
    _ = (pairTypeGroup parents coordinate bitType).card :=
      Fintype.card_coe _

theorem pairChildArraysOfProfile_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : PairTypeCountProfile parentCount dimension) :
    (pairChildArraysOfProfile parents profile).card =
      ∏ index : PairBitType × Fin dimension,
        ((pairTypeGroup parents index.2 index.1).card).choose
          (profile index.1 index.2).val := by
  calc
    (pairChildArraysOfProfile parents profile).card =
      Fintype.card ↥(pairChildArraysOfProfile parents profile) :=
        (Fintype.card_coe _).symm
    _ = Fintype.card
      ↥(classifiedBooleanWords
        (pairCoordinateClassification parents)
        (fun index : PairBitType × Fin dimension =>
          (profile index.1 index.2).val)) :=
        Fintype.card_congr
          (pairChildArraysOfProfileEquiv parents profile)
    _ = (classifiedBooleanWords
        (pairCoordinateClassification parents)
        (fun index : PairBitType × Fin dimension =>
          (profile index.1 index.2).val)).card :=
        Fintype.card_coe _
    _ = ∏ index : PairBitType × Fin dimension,
        (Fintype.card
          (ClassificationFiber
            (pairCoordinateClassification parents) index)).choose
          (profile index.1 index.2).val :=
        classifiedBooleanWords_card
          (pairCoordinateClassification parents)
          (fun index : PairBitType × Fin dimension =>
            (profile index.1 index.2).val)
    _ = ∏ index : PairBitType × Fin dimension,
        ((pairTypeGroup parents index.2 index.1).card).choose
          (profile index.1 index.2).val := by
      apply Finset.prod_congr rfl
      rintro ⟨bitType, coordinate⟩ _
      rw [pairCoordinateClassificationFiber_card]

theorem pairCoordinateConditionalEntropy_mass
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (parentCount.choose 2 : ℝ) *
        pairCoordinateConditionalEntropy parents children coordinate =
      ∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) *
          binaryEntropy
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ)) := by
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  unfold pairCoordinateConditionalEntropy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bitType _
  field_simp [hpair.ne']

theorem pairCoordinateConditionalEntropy_log_mass
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : PairBitType,
      ((pairTypeGroup parents coordinate bitType).card : ℝ) *
        Real.binEntropy
          (((pairTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
            ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
      (parentCount.choose 2 : ℝ) * Real.log 2 *
        pairCoordinateConditionalEntropy parents children coordinate := by
  calc
    (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) *
          Real.binEntropy
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
      (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) *
          binaryEntropy
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) *
        Real.log 2 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro bitType _
          unfold binaryEntropy
          field_simp [log_two_pos.ne']
    _ = (parentCount.choose 2 : ℝ) * Real.log 2 *
        pairCoordinateConditionalEntropy parents children coordinate := by
      rw [← pairCoordinateConditionalEntropy_mass
        hparents parents children coordinate]
      ring

theorem pairChildGroup_choose_product_entropy_bound
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    (∏ index : PairBitType × Fin dimension,
      ((pairTypeGroup parents index.2 index.1).card).choose
        ((pairTypeGroupChildOnes parents children index.2 index.1).card) : ℝ) ≤
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate)) := by
  have hproduct := choose_product_le_exp_binary_entropy
    (ι := PairBitType × Fin dimension)
    (fun index => (pairTypeGroup parents index.2 index.1).card)
    (fun index =>
      (pairTypeGroupChildOnes parents children index.2 index.1).card)
    (fun index => pairTypeGroupChildOnes_card_le
      parents children index.2 index.1)
  have hsum :
      (∑ index : PairBitType × Fin dimension,
        ((pairTypeGroup parents index.2 index.1).card : ℝ) *
          Real.binEntropy
            (((pairTypeGroupChildOnes parents children
                index.2 index.1).card : ℝ) /
              ((pairTypeGroup parents index.2 index.1).card : ℝ))) =
        (parentCount.choose 2 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [pairCoordinateConditionalEntropy_log_mass
      hparents parents children]
    rw [Finset.mul_sum]
  rw [hsum] at hproduct
  exact hproduct

theorem pairChildArraysOfRealizedProfile_card_le
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    ((pairChildArraysOfProfile parents
        (pairChildCountProfile parents children)).card : ℝ) ≤
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate)) := by
  have hcard :
      ((pairChildArraysOfProfile parents
        (pairChildCountProfile parents children)).card : ℝ) =
        ∏ index : PairBitType × Fin dimension,
          (((pairTypeGroup parents index.2 index.1).card).choose
            ((pairTypeGroupChildOnes parents children
              index.2 index.1).card) : ℝ) := by
    exact_mod_cast
      pairChildArraysOfProfile_card parents
        (pairChildCountProfile parents children)
  rw [hcard]
  exact pairChildGroup_choose_product_entropy_bound
    hparents parents children

theorem badPairChildArrays_card_le
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (threshold : ℝ) :
    ((badPairChildArrays parents threshold).card : ℝ) ≤
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold) := by
  classical
  let bound : ℝ :=
    Real.exp
      ((parentCount.choose 2 : ℝ) * Real.log 2 *
        (dimension : ℝ) * threshold)
  have hbound_nonneg : 0 ≤ bound := by
    dsimp [bound]
    exact (Real.exp_pos _).le
  have hmaps :
      ((badPairChildArrays parents threshold :
        Finset (PairLayer parentCount 1 → HammingWord dimension)) :
        Set (PairLayer parentCount 1 → HammingWord dimension)).MapsTo
        (pairChildCountProfile parents)
        (Finset.univ : Finset (PairTypeCountProfile parentCount dimension)) := by
    intro children _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (profile : PairTypeCountProfile parentCount dimension) :
      (((badPairChildArrays parents threshold).filter
        (fun children => pairChildCountProfile parents children = profile)).card : ℝ) ≤
        bound := by
    by_cases hnonempty :
        ((badPairChildArrays parents threshold).filter
          (fun children =>
            pairChildCountProfile parents children = profile)).Nonempty
    · obtain ⟨children, hchildren⟩ := hnonempty
      have hparts := Finset.mem_filter.mp hchildren
      have hprofile : pairChildCountProfile parents children = profile :=
        hparts.2
      have hbad : pairChildArrayEntropy parents children ≤ threshold := by
        have hmembership :
            children ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 →
                    HammingWord dimension =>
                  pairChildArrayEntropy parents candidate ≤ threshold)) := by
          simpa only [badPairChildArrays] using hparts.1
        exact (Finset.mem_filter.mp hmembership).2
      have hsubset :
          (badPairChildArrays parents threshold).filter
              (fun candidate =>
                pairChildCountProfile parents candidate = profile) ⊆
            pairChildArraysOfProfile parents profile := by
        intro candidate hcandidate
        have hcandidate_profile := (Finset.mem_filter.mp hcandidate).2
        unfold pairChildArraysOfProfile
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hcandidate_profile⟩
      have hcard :
          (((badPairChildArrays parents threshold).filter
            (fun candidate =>
              pairChildCountProfile parents candidate = profile)).card : ℝ) ≤
            ((pairChildArraysOfProfile parents profile).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      have hrealized :
          ((pairChildArraysOfProfile parents profile).card : ℝ) ≤
            Real.exp
              ((parentCount.choose 2 : ℝ) * Real.log 2 *
                (∑ coordinate : Fin dimension,
                  pairCoordinateConditionalEntropy
                    parents children coordinate)) := by
        rw [← hprofile]
        exact pairChildArraysOfRealizedProfile_card_le
          hparents parents children
      have hdimension_real : 0 < (dimension : ℝ) := by
        exact_mod_cast hdimension
      have hsum :
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate) ≤
              (dimension : ℝ) * threshold := by
        unfold pairChildArrayEntropy at hbad
        have hcleared := (div_le_iff₀ hdimension_real).mp hbad
        nlinarith
      have hcoefficient :
          0 ≤ (parentCount.choose 2 : ℝ) * Real.log 2 :=
        mul_nonneg (Nat.cast_nonneg _) log_two_pos.le
      have hexponential :
          Real.exp
              ((parentCount.choose 2 : ℝ) * Real.log 2 *
                (∑ coordinate : Fin dimension,
                  pairCoordinateConditionalEntropy
                    parents children coordinate)) ≤ bound := by
        dsimp [bound]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hsum hcoefficient]
      exact hcard.trans (hrealized.trans hexponential)
    · have hempty :
          (badPairChildArrays parents threshold).filter
            (fun children =>
              pairChildCountProfile parents children = profile) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hnonempty
      simpa [hempty] using hbound_nonneg
  calc
    ((badPairChildArrays parents threshold).card : ℝ) =
        ∑ profile : PairTypeCountProfile parentCount dimension,
          (((badPairChildArrays parents threshold).filter
            (fun children =>
              pairChildCountProfile parents children = profile)).card : ℝ) := by
      exact_mod_cast hpartition
    _ ≤ ∑ _profile : PairTypeCountProfile parentCount dimension, bound := by
      exact Finset.sum_le_sum (fun profile _ => hfiber profile)
    _ = (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
          Real.exp
            ((parentCount.choose 2 : ℝ) * Real.log 2 *
              (dimension : ℝ) * threshold) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        pairTypeCountProfile_card]

theorem pairChildVertexFinset_card
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (hinjective : Function.Injective children) :
    (pairChildVertexFinset side children).card = parentCount.choose 2 := by
  classical
  unfold pairChildVertexFinset
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ, pairLayer_card_succ parentCount 0,
      pairLayer_card_zero]
  · intro first second hequal
    exact hinjective (congrArg Prod.snd hequal)

theorem hammingRetentionMeasure_real_pairChildren
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (hinjective : Function.Injective children) :
    (hammingRetentionMeasure dimension).real
        (pairChildRetentionEvent side children) =
      hammingRetentionProbability dimension ^ (parentCount.choose 2) := by
  classical
  have hevent :
      pairChildRetentionEvent side children =
        {retained : Set (Bool × HammingWord dimension) |
          ∀ vertex ∈ pairChildVertexFinset side children,
            vertex ∈ retained} := by
    ext retained
    simp [pairChildRetentionEvent, pairChildVertexFinset]
  rw [hevent, hammingRetentionMeasure_real_contains_finset,
    pairChildVertexFinset_card side children hinjective]

theorem badPairChildRetentionEvent_real_le
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (side : Bool)
    (threshold : ℝ) :
    (hammingRetentionMeasure dimension).real
        (badPairChildRetentionEvent parents side threshold) ≤
      ((((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
  classical
  let distinctBad :
      Finset (PairLayer parentCount 1 → HammingWord dimension) :=
    (badPairChildArrays parents threshold).filter Function.Injective
  have hprobability_nonneg :
      0 ≤ hammingRetentionProbability dimension ^
        (parentCount.choose 2) :=
    pow_nonneg (hammingRetentionProbability_pos dimension).le _
  have hcard :
      (distinctBad.card : ℝ) ≤
        ((badPairChildArrays parents threshold).card : ℝ) := by
    dsimp [distinctBad]
    exact_mod_cast
      Finset.card_filter_le
        (badPairChildArrays parents threshold) Function.Injective
  calc
    (hammingRetentionMeasure dimension).real
        (badPairChildRetentionEvent parents side threshold) =
      (hammingRetentionMeasure dimension).real
        (⋃ children ∈ distinctBad,
          pairChildRetentionEvent side children) := by
        rfl
    _ ≤ ∑ children ∈ distinctBad,
          (hammingRetentionMeasure dimension).real
            (pairChildRetentionEvent side children) :=
        MeasureTheory.measureReal_biUnion_finset_le
          distinctBad (pairChildRetentionEvent side)
    _ = ∑ _children ∈ distinctBad,
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
        apply Finset.sum_congr rfl
        intro children hchildren
        have hinjective : Function.Injective children := by
          have hmembership :
              children ∈
                (badPairChildArrays parents threshold).filter
                  Function.Injective := by
            simpa only [distinctBad] using hchildren
          exact (Finset.mem_filter.mp hmembership).2
        exact hammingRetentionMeasure_real_pairChildren
          side children hinjective
    _ = (distinctBad.card : ℝ) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
        simp [nsmul_eq_mul]
    _ ≤ ((badPairChildArrays parents threshold).card : ℝ) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) :=
        mul_le_mul_of_nonneg_right hcard hprobability_nonneg
    _ ≤
      ((((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) :=
        mul_le_mul_of_nonneg_right
          (badPairChildArrays_card_le hparents hdimension parents threshold)
          hprobability_nonneg

theorem hammingParentTuple_card (parentCount dimension : ℕ) :
    Fintype.card (Fin parentCount → HammingWord dimension) =
      2 ^ (dimension * parentCount) := by
  simp [HammingWord, ← pow_mul]

theorem badPairLayerRetentionEvent_real_le
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (hdimension : 0 < dimension)
    (side : Bool)
    (threshold : ℝ) :
    (hammingRetentionMeasure dimension).real
        (badPairLayerRetentionEvent parentCount dimension side threshold) ≤
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
  classical
  let bound : ℝ :=
    ((((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (dimension : ℝ) * threshold)) *
        hammingRetentionProbability dimension ^
          (parentCount.choose 2)
  calc
    (hammingRetentionMeasure dimension).real
        (badPairLayerRetentionEvent parentCount dimension side threshold) =
      (hammingRetentionMeasure dimension).real
        (⋃ parents : Fin parentCount → HammingWord dimension,
          badPairChildRetentionEvent parents side threshold) := by
        rfl
    _ ≤ ∑ parents : Fin parentCount → HammingWord dimension,
          (hammingRetentionMeasure dimension).real
            (badPairChildRetentionEvent parents side threshold) :=
        MeasureTheory.measureReal_iUnion_fintype_le
          (fun parents => badPairChildRetentionEvent parents side threshold)
    _ ≤ ∑ _parents : Fin parentCount → HammingWord dimension, bound := by
      apply Finset.sum_le_sum
      intro parents _
      exact badPairChildRetentionEvent_real_le
        hparents hdimension parents side threshold
    _ =
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        hammingParentTuple_card]
      dsimp [bound]
      ring

theorem badPairLayerRetentionBound_eq_exp
    (parentCount dimension : ℕ) :
    ((((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (dimension : ℝ) * (midpointBeta - entropySlack))) *
        hammingRetentionProbability dimension ^
          (parentCount.choose 2)) =
      Real.exp
        ((dimension : ℝ) * Real.log 2 *
          ((parentCount : ℝ) +
            3 * logTwo ((parentCount.choose 2 + 1 : ℕ) : ℝ) -
              entropySlack * (parentCount.choose 2 : ℝ))) := by
  have hparent :
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ)) =
        Real.exp
          (((dimension * parentCount : ℕ) : ℝ) * Real.log 2) := by
    calc
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ)) =
          (2 : ℝ) ^ (dimension * parentCount) := by
            norm_cast
      _ = Real.exp
          (((dimension * parentCount : ℕ) : ℝ) * Real.log 2) := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hprofile :
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) =
        Real.exp
          (((3 * dimension : ℕ) : ℝ) *
            Real.log ((parentCount.choose 2 + 1 : ℕ) : ℝ)) := by
    calc
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) =
          (((parentCount.choose 2 + 1 : ℕ) : ℝ)) ^
            (3 * dimension) := by
              norm_cast
      _ = Real.exp
          (((3 * dimension : ℕ) : ℝ) *
            Real.log ((parentCount.choose 2 + 1 : ℕ) : ℝ)) := by
              rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hretention :
      hammingRetentionProbability dimension ^
          (parentCount.choose 2) =
        Real.exp
          ((parentCount.choose 2 : ℝ) *
            (-(midpointBeta * (dimension : ℝ) * Real.log 2))) := by
    unfold hammingRetentionProbability
    rw [Real.exp_nat_mul]
  rw [hparent, hprofile, hretention,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply congrArg Real.exp
  unfold logTwo
  push_cast
  field_simp [log_two_pos.ne']
  ring

theorem badPairLayerRetentionEvent_real_lt_exp_neg
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (hbase :
      (parentCount : ℝ) +
        3 * logTwo ((parentCount.choose 2 + 1 : ℕ) : ℝ) -
          entropySlack * (parentCount.choose 2 : ℝ) < -1)
    (side : Bool) :
    (hammingRetentionMeasure dimension).real
      (badPairLayerRetentionEvent parentCount dimension side
        (midpointBeta - entropySlack)) <
      Real.exp (-(dimension : ℝ) * Real.log 2) := by
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  calc
    (hammingRetentionMeasure dimension).real
      (badPairLayerRetentionEvent parentCount dimension side
        (midpointBeta - entropySlack)) ≤
      ((((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * (midpointBeta - entropySlack))) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2)) :=
        badPairLayerRetentionEvent_real_le
          (by omega) hdimension side (midpointBeta - entropySlack)
    _ = Real.exp
        ((dimension : ℝ) * Real.log 2 *
          ((parentCount : ℝ) +
            3 * logTwo ((parentCount.choose 2 + 1 : ℕ) : ℝ) -
              entropySlack * (parentCount.choose 2 : ℝ))) :=
        badPairLayerRetentionBound_eq_exp parentCount dimension
    _ < Real.exp (-(dimension : ℝ) * Real.log 2) := by
      apply Real.exp_lt_exp.mpr
      have hscaled := mul_lt_mul_of_pos_left hbase
        (mul_pos hdimension_real log_two_pos)
      nlinarith

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    {depth dimension : ℕ}
    (layerSizes : Fin depth → ℕ)
    (hdimension : 0 < dimension)
    (hparents : ∀ layer, 4 ≤ layerSizes layer)
    (hbase : ∀ layer,
      (layerSizes layer : ℝ) +
        3 * logTwo
          (((layerSizes layer).choose 2 + 1 : ℕ) : ℝ) -
          entropySlack * ((layerSizes layer).choose 2 : ℝ) < -1) :
    (hammingRetentionMeasure dimension).real
        (badPairLayersRetentionEvent layerSizes dimension) ≤
      (((2 * depth : ℕ) : ℝ)) *
        Real.exp (-(dimension : ℝ) * Real.log 2) := by
  classical
  let bound : ℝ := Real.exp (-(dimension : ℝ) * Real.log 2)
  calc
    (hammingRetentionMeasure dimension).real
        (badPairLayersRetentionEvent layerSizes dimension) =
      (hammingRetentionMeasure dimension).real
        (⋃ side : Bool, ⋃ layer : Fin depth,
          badPairLayerRetentionEvent (layerSizes layer) dimension side
            (midpointBeta - entropySlack)) := by
        rfl
    _ ≤ ∑ side : Bool,
        (hammingRetentionMeasure dimension).real
          (⋃ layer : Fin depth,
            badPairLayerRetentionEvent (layerSizes layer) dimension side
              (midpointBeta - entropySlack)) :=
        MeasureTheory.measureReal_iUnion_fintype_le
          (fun side =>
            ⋃ layer : Fin depth,
              badPairLayerRetentionEvent (layerSizes layer) dimension side
                (midpointBeta - entropySlack))
    _ ≤ ∑ side : Bool, ∑ layer : Fin depth,
          (hammingRetentionMeasure dimension).real
            (badPairLayerRetentionEvent
              (layerSizes layer) dimension side
                (midpointBeta - entropySlack)) := by
        apply Finset.sum_le_sum
        intro side _
        exact MeasureTheory.measureReal_iUnion_fintype_le
          (fun layer =>
            badPairLayerRetentionEvent
              (layerSizes layer) dimension side
                (midpointBeta - entropySlack))
    _ ≤ ∑ _side : Bool, ∑ _layer : Fin depth, bound := by
        apply Finset.sum_le_sum
        intro side _
        apply Finset.sum_le_sum
        intro layer _
        exact (badPairLayerRetentionEvent_real_lt_exp_neg
          (hparents layer) hdimension (hbase layer) side).le
    _ = (((2 * depth : ℕ) : ℝ)) *
          Real.exp (-(dimension : ℝ) * Real.log 2) := by
        simp [bound, nsmul_eq_mul]
        ring
