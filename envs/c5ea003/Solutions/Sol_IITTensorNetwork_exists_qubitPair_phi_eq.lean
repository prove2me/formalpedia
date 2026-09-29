-- Prove2me | solution 1 for IITTensorNetwork.exists_qubitPair_phi_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T10:55:44.13002+00:00
-- url     : https://prove2.me/submissions/68261625-50f8-4de8-853b-45792f35cff6

-- Sol generated from Novelty/IITTensorNetworkPhiSpectrum.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IITTensorNetworkSchmidtSpectrum
import Theorems.Thm_IITTensorNetwork_phi_qubitPair
import Theorems.Thm_IITTensorNetwork_qubitPairState_normalized

/-! # The spectrum of `Φ` at bond dimension two

For two-qubit chain states the integrated information satisfies
`0 ≤ Φ ≤ 2 log 2` (`phi_two_qubits_le_two_log_two`), the upper bound coming from
the Schmidt rank cap.  Here we prove the converse: **every** value of the
interval `[0, 2 log 2]` is attained, already by the one-parameter family
`c|00⟩ + s|11⟩` of `IITTensorNetworkSchmidtSpectrum.lean`.  Thus the set of
values of `Φ` on two-qubit states is exactly `[0, 2 log 2]`, which is the
`n = d = χ = 2` case of the "spectrum of `Φ` is a full interval" question.

Main results:

* `phi_two_qubits_le_two_log_two` — the cap `Φ ≤ 2 log 2` for any two-qubit state;
* `exists_qubitPair_phi_eq` — every `t ∈ [0, 2 log 2]` is the `Φ` of some state
  `c|00⟩ + s|11⟩`;
* `phi_range_qubitPair` — the range of `Φ` on the family is exactly `[0, 2 log 2]`.
-/

open Set

open IITTensorNetwork




/-- `Φ` of the two-qubit family, in terms of the binary entropy of `c²`. -/
theorem phi_qubitPair_binEntropy {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    Phi (qubitPairState_normalized h) (le_refl 2) = 2 * Real.binEntropy (c ^ 2) := by
  rw [phi_qubitPair h, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have hs : s ^ 2 = 1 - c ^ 2 := by linarith
  rw [hs]





open IITTensorNetwork in
theorem solution{t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (2 * Real.log 2)) :
    ∃ (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1),
      Phi (qubitPairState_normalized h) (le_refl 2) = t := by
  have hcont : ContinuousOn (fun p : ℝ => 2 * Real.binEntropy p) (Set.Icc 0 2⁻¹) :=
    (continuous_const.mul Real.binEntropy_continuous).continuousOn
  have hsub := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 2⁻¹) hcont
  have hmem : t ∈ Set.Icc ((fun p : ℝ => 2 * Real.binEntropy p) 0)
      ((fun p : ℝ => 2 * Real.binEntropy p) 2⁻¹) := by
    simpa using ht
  obtain ⟨p, hp, hpt⟩ := hsub hmem
  obtain ⟨hp0, hp1⟩ := hp
  have hp1' : p ≤ 1 := by linarith
  have hnorm : Real.sqrt p ^ 2 + Real.sqrt (1 - p) ^ 2 = 1 := by
    rw [Real.sq_sqrt hp0, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - p)]
    ring
  refine ⟨Real.sqrt p, Real.sqrt (1 - p), hnorm, ?_⟩
  rw [phi_qubitPair_binEntropy hnorm, Real.sq_sqrt hp0]
  simpa using hpt
