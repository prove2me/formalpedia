-- Prove2me | Theorems.Thm_pac_lower_bound_member
-- name    : pac_lower_bound_member
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:40.834026+00:00
-- url     : https://prove2.me/theorems/e1533336-4016-4e93-9150-10cce0769fcb
-- title:
--   pac lower bound member: pac lower bound member
-- statement:
--   PAC lower bound membership: if m achieves PAC for C with VCDim = d,
--       then m ≥ ⌈(d-1)/(64ε)⌉.
--       This is the core adversarial counting argument factored for PAC.lean assembly.
--       Note: the tight constant is (d-1)/(2ε) (EHKV 1989); see EHKV.lean.
--
--       Proof route (double-averaging on shattered set):
--       1. VCDim = d → ∃ shattered S with |S| = d
--       2. D = uniform on S (probability measure, each point has weight 1/d)
--       3. m < ⌈(d-1)/(64ε)⌉ → 2m < d → NFL counting applies
--       4. Double-averaging over 2^d labelings: E_f[E_xs[error]] ≥ (d-m)/(2d) > 1 / 4
--       5. Reversed Markov: ∃ c₀ ∈ C with Pr[error ≤ 1 / 8] ≤ 6 / 7
--       6. For ε ≤ 1 / 8: Pr[error ≤ ε] ≤ 6 / 7 = 1 - 1 / 7, contradicting PAC
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L2088-L2182
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L2088-L2182

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem pac_lower_bound_member (X : Type u) [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (d : ℕ)
    (hd : VCDim X C = d) (ε δ : ℝ) (_hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hδ : 0 < δ) (_hδ1 : δ ≤ 1) (hδ2 : δ ≤ 1 / 7) (hd_pos : 1 ≤ d) (m : ℕ)
    (hm : m ∈ { m : ℕ | ∃ (L : BatchLearner X Bool),
      ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
        ∀ c ∈ C,
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal ε }
            ≥ ENNReal.ofReal (1 - δ) }) :
    Nat.ceil ((d - 1 : ℝ) / 2) ≤ m := by sorry
