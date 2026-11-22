-- Prove2me | Theorems.Thm_baxter_full
-- name    : baxter_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:42:16.860139+00:00
-- url     : https://prove2.me/theorems/fcba08e8-f4be-462d-afc8-811c85f4a461
-- title:
--   baxter full: baxter full
-- statement:
--   Baxter's multi-task lower bound: any sample-based meta-learner
--       that achieves PAC on a new task C_new with VCDim = d, after seeing
--       n training tasks with m samples each, requires ⌈(d-1)/2⌉ samples
--       for the new task.
--
--       This is the n-independent version. The n-dependent improvement
--       m ≥ Ω(d/(ε²·n)) requires the product-measure information-theoretic
--       argument.
--
--       Key insight: the meta-learner's output (L, mf) is a PAC witness
--       for C_new. By pac_lower_bound_member, any PAC witness requires
--       at least ⌈(d-1)/2⌉ samples. The meta-learner's training phase
--       (seeing n tasks) cannot reduce this bound because the new task's
--       concept class is adversarially chosen AFTER training.
--
--       The n-dependent improvement (Baxter 2000, Theorem 3):
--       For the PRODUCT measure over n tasks × m samples per task,
--       the adversary argument gives m ≥ Ω(d/(ε²·n)).
--       This requires:
--       - TaskDistribution: a measure over concept classes
--       - Product measure: D^(n×m) decomposed as (D^m)^n
--       - Information-theoretic counting: n·m bits vs 2^d labelings
--       This theorem proves the n-independent base case.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Extended.lean#L1027-L1047
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Extended.lean#L1027-L1047

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Extended
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem baxter_full (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (SML : SampleMetaLearner X)
    (C_new : ConceptClass X Bool)
    (d : ℕ) (hd : VCDim X C_new = d) (hd_pos : 1 ≤ d)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδ2 : δ ≤ 1 / 7)
    (n m : ℕ)
    (training_data : Fin n → Fin m → X × Bool)
    (hPAC : ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ c ∈ C_new,
        let mf := SML.sampleComplexity n m ε δ
        MeasureTheory.Measure.pi
          (fun _ : Fin mf => D)
          { xs : Fin mf → X |
            D { x | (SML.learn training_data).learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal ε }
          ≥ ENNReal.ofReal (1 - δ)) :
    Nat.ceil ((d - 1 : ℝ) / 2) ≤ SML.sampleComplexity n m ε δ := by sorry
