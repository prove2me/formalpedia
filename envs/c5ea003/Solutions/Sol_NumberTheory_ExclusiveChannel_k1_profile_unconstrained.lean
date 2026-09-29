-- Prove2me | solution 1 for NumberTheory.ExclusiveChannel.k1_profile_unconstrained
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:00:00.325886+00:00
-- url     : https://prove2.me/submissions/a229e0b4-1178-432b-95aa-21b9d30a6d85

-- Sol generated from NumberTheory/ExclusiveChannelPopulation.lean
import Mathlib
import Definitions.Def_NumberTheory_ExclusiveChannelInterventions
import Definitions.Def_NumberTheory_ExclusiveChannelPopulation
import Theorems.Thm_NumberTheory_ExclusiveChannel_satGate_zeroAll
import Theorems.Thm_NumberTheory_ExclusiveChannel_zeroAt_eq_zeroAll_of_one
/-
# NET-30 / Catalog·NumberTheory — A saturating-gate population model: the k = 2
signature realised, and the k = 1 arms shown to be unconstrained

The two companion files are *negative*: the measured s = 13, k = 2 signature
(single-coordinate ablations inside the no-op band, whole-block ablation costing
0.24, sign flip costing as much) is impossible for an affine read-out
(`NumberTheory.ExclusiveChannelInterventions`) and, more sharply, for any convex
one (`NumberTheory.ExclusiveChannelConvexity`).  This file supplies the matching
*positive* half: an explicit, fully computed model in which the entire published
NET-30 s = 13 row is reproduced, and a theorem showing the Part B (`k = 1`) rows
carry no information at all about the model class.

Ingredients.

* `ItemPopulation`: a finite population of evaluation items with masses summing
  to `1`, item `i` being answered correctly exactly when the boundary gate value
  reaches its difficulty threshold `thr i`.  `ItemPopulation.acc γ` is the
  accuracy at gate value `γ`; it is monotone in `γ` (`acc_mono`).
* `satGate`: the saturating boundary gate `min (max (∑ i, c i) 0) 1` on the
  exclusive coefficients — rectified (hence sign-sensitive) and saturating
  (hence redundant).
* `s13_k2_saturating_realization`: one population, one coefficient vector
  `c = ![1, 1]`, and **all six** published s = 13 arm numbers reproduced to
  within `0.005` (the reported no-op scale): `ctl 0.9980`, `zeroAt 0 0.9961`,
  `zeroAt 1 0.9990`, `zeroAll 0.7544`, `flipAt 0 0.7505`, `scale 0.1 0.9067`.
  The model *predicts* the exact no-op of both single ablations and the
  simultaneous sign- and magnitude-sensitivity, which is what the arm shows.
* `acc_scaleAll_mono`: the scale curve is monotone, so `zeroAll ≤ scale l ≤ ctl`
  — matching the measured `0.7544 ≤ 0.9067 ≤ 0.9980` ordering.
* `missing_middle_sharp`: the headline. In this model class the
  "1-redundant but block-dependent" phenomenon **occurs at k = 2** and
  **cannot occur at k ≤ 1** — the formal statement of "the missing middle".
* `interventions_noop_of_boundary_free`, `noop_all_iff_acc_zero_eq`: a
  boundary-free arm (control accuracy already equal to the zero-gate accuracy)
  is unchanged by every gate-weakening intervention, and that is the *only* way
  for all of them to be no-ops.  This is the pooled Part B invariant — the
  failed arms are no-ops in every arm of both rounds — and it shows such a
  no-op is evidence that the channel was never used, not of internalisation.
* `k1_profile_unconstrained`: at `k = 1` *every* admissible pair of control and
  ablation accuracies `0 ≤ β ≤ α ≤ 1` is realised by some population.  The
  seed-heterogeneous Part B outcomes (two exact self-sufficient cures, two
  no-ops, two ~2 SE marginal losses) are therefore all inside the same class:
  no `k = 1` observation constrains it, which is precisely why the
  proportionality law it was used to support does not survive.
-/


open NumberTheory.ExclusiveChannel

open Finset

/-! ## Populations of evaluation items -/




/-! ## The saturating boundary gate -/






/-! ## Gate values of the six s = 13 interventions at `c = ![1, 1]` -/






/-! ## The s = 13 population -/










/-! ## The missing middle, sharp -/



/-! ## Why the failed arms are no-ops in every intervention

Pooled over all twelve `k = 1` arms of NET-29 and NET-30, removal of the sole
exclusive coordinate is a no-op *in every arm where the model had already
failed*.  In the population model this is forced: an arm whose accuracy is
already the boundary-free accuracy `acc 0` has no gate-dependent mass among the
items it solves, so weakening the gate — by ablation, by a partial ablation, or
by rescaling — cannot cost anything. -/







/-! ## Part B: the k = 1 rows constrain nothing -/



open NumberTheory.ExclusiveChannel in
theorem solution{α β : ℝ} (hβ : 0 ≤ β) (hβα : β ≤ α) (hα : α ≤ 1) :
    ∃ (P : ItemPopulation) (c : Fin 1 → ℝ),
      P.acc (satGate c) = α ∧ P.acc (satGate (zeroAll c)) = β ∧
        ∀ i, P.acc (satGate (zeroAt i c)) = β := by
  refine ⟨⟨3, ![β, α - β, 1 - α], ![0, 1, 2], ?_, ?_⟩, ![1], ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp <;> linarith
  · norm_num [Fin.sum_univ_succ]
  · have hg : satGate (![1] : Fin 1 → ℝ) = 1 := by
      simp [satGate]
    rw [hg]
    show (∑ x : Fin 3, if (![0, 1, 2] : Fin 3 → ℝ) x ≤ 1 then (![β, α - β, 1 - α] : Fin 3 → ℝ) x else 0) = α
    norm_num [Fin.sum_univ_succ]
  · rw [satGate_zeroAll]
    show (∑ x : Fin 3, if (![0, 1, 2] : Fin 3 → ℝ) x ≤ 0 then (![β, α - β, 1 - α] : Fin 3 → ℝ) x else 0) = β
    norm_num [Fin.sum_univ_succ]
  · intro i
    rw [zeroAt_eq_zeroAll_of_one _ i, satGate_zeroAll]
    show (∑ x : Fin 3, if (![0, 1, 2] : Fin 3 → ℝ) x ≤ 0 then (![β, α - β, 1 - α] : Fin 3 → ℝ) x else 0) = β
    norm_num [Fin.sum_univ_succ]
