-- Prove2me | Theorems.Thm_IITTensorNetwork_exists_qubitPair_phi_eq
-- name    : IITTensorNetwork.exists_qubitPair_phi_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T10:25:51.66296+00:00
-- url     : https://prove2.me/theorems/d9ccedf0-4b7e-443c-9f3c-e351a8856b17
-- title:
--   Every value in `[0, 2 log 2]` is attained.
-- statement:
--   **Every value in `[0, 2 log 2]` is attained.**  Given `t` between `0` and
--   `2 log 2` there is a two-qubit state `c|00⟩ + s|11⟩` with `Φ = t`.
--
--   ```lean
--   theorem IITTensorNetwork.exists_qubitPair_phi_eq{t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (2 * Real.log 2)) :
--       ∃ (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1),
--         Phi (qubitPairState_normalized h) (le_refl 2) = t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IITTensorNetworkPhiSpectrum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IITTensorNetworkPhiSpectrum.lean#L54

-- Thm stub generated from Novelty/IITTensorNetworkPhiSpectrum.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IITTensorNetworkSchmidtSpectrum
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

theorem IITTensorNetwork.exists_qubitPair_phi_eq{t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (2 * Real.log 2)) :
    ∃ (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1),
      Phi (qubitPairState_normalized h) (le_refl 2) = t := by sorry
