-- Prove2me | Theorems.Thm_baxter_base_case
-- name    : baxter_base_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:42:12.003864+00:00
-- url     : https://prove2.me/theorems/7cb5884b-ed91-4931-8378-c1f2b524540e
-- title:
--   baxter base case: baxter base case
-- statement:
--   Baxter base case: any meta-learner's output is subject to the NFL lower bound.
--       Even after seeing arbitrarily many training tasks, the meta-learner's output
--       learner on a NEW task C_new with VCDim = d requires at least ⌈(d-1)/2⌉ samples.
--
--       This is the n=1 (single environment) base case of Baxter (2000).
--       The full Baxter bound (n environments, per-task m ≥ d/(ε²·n)) requires
--       multi-environment product measure infrastructure not yet built.
--
--       Proof: the meta-learner produces a BatchLearner L and sample complexity mf.
--       If (L, mf) achieves PAC on C_new, then mf ε δ is a PAC-valid sample size,
--       so pac_lower_bound_member gives ⌈(d-1)/2⌉ ≤ mf ε δ.
--
--       The full multi-environment Baxter bound is outside this kernel; this theorem
--       records the single-environment lower-bound component.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Extended.lean#L984-L1002
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Extended.lean#L984-L1002

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

theorem baxter_base_case (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (ML : MetaLearnerPAC X)
    (env : TaskEnvironment X)
    (C_new : ConceptClass X Bool)
    (d : ℕ) (hd : VCDim X C_new = d) (hd_pos : 1 ≤ d)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδ2 : δ ≤ 1 / 7)
    (hPAC : ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ c ∈ C_new,
        MeasureTheory.Measure.pi
          (fun _ : Fin (ML.sampleComplexity env ε δ) => D)
          { xs : Fin (ML.sampleComplexity env ε δ) → X |
            D { x | (ML.learn env).learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal ε }
          ≥ ENNReal.ofReal (1 - δ)) :
    Nat.ceil ((d - 1 : ℝ) / 2) ≤ ML.sampleComplexity env ε δ := by sorry
