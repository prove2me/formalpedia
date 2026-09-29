-- Prove2me | Theorems.Thm_mme_coupled_trace_power_restriction_word_basis_maps
-- name    : mme_coupled_trace_power_restriction_word_basis_maps
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T02:38:56.499474+00:00
-- url     : https://prove2.me/theorems/ee0a9d3a-8dc1-46a0-b6f5-164331ae9d07
-- title:
--   Trace restriction maps act letter by letter on coupled tensor powers
-- statement:
--   Let $K$ be any field and $q$ a nonnegative integer. There exist coordinate maps from the coupled constituent $C_q$ to the matrix tensor $\langle 1,2q,1\rangle$ that carry every tensor power of $C_q$ to the corresponding matrix-tensor power. Their action on the first two coordinate word bases is explicit: the first map sends each letter $x\in\operatorname{Fin}(q)\sqcup\operatorname{Fin}(q)$ to $(0,e(x))$, while the second sends it to $(e(\operatorname{swap}(x)),0)$, where $e$ is the canonical enumeration of the disjoint union. Both formulas act independently at every word position, including the empty word. Thus the trace restriction retains the numerical letters and specifies the binary-label swap. This statement concerns the unrestricted source powers; descent through allowed-word projections is a separate requirement.
-- source:
--   Explicit diagonal trace construction for the coupled constituent, followed by tensor-power functoriality and induction on the recursive word basis.

import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Mathlib.Tactic.FinCases

open MME MME.DWZComponentRestriction PiTensorProduct Module TensorProduct BigOperators
universe u
set_option autoImplicit false

theorem mme_coupled_trace_power_restriction_word_basis_maps
    {K : Type u} [Field K] (q : ℕ) :
    let T := coupledObj K q
    let S := MMObj K 1 (q + q) 1
    let b0 := (Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm
    let b1 := (Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm
    let c0 := (Pi.basisFun K (Fin 1 × Fin (q + q))).reindex Equiv.ulift.symm
    let c1 := (Pi.basisFun K (Fin (q + q) × Fin 1)).reindex Equiv.ulift.symm
    ∃ f : ∀ i, T.V i →ₗ[K] S.V i,
      (∀ N, PiTensorProduct.map (fun i ↦ TensorObj.kronPowModeMap i (f i) N)
        (T.kronPow N).t = (S.kronPow N).t) ∧
      (∀ N (w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N),
        TensorObj.kronPowModeMap 0 (f 0) N (kronPowModeBasis T 0 b0 N w) =
          kronPowModeBasis S 0 c0 N (PowIndex.ofFun N (fun r ↦
            (⟨(0, finSumFinEquiv (PowIndex.get N w r).down)⟩ :
              ULift.{u} (Fin 1 × Fin (q + q)))))) ∧
      (∀ N (w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N),
        TensorObj.kronPowModeMap 1 (f 1) N (kronPowModeBasis T 1 b1 N w) =
          kronPowModeBasis S 1 c1 N (PowIndex.ofFun N (fun r ↦
            (⟨(finSumFinEquiv (Sum.swap (PowIndex.get N w r).down), 0)⟩ :
              ULift.{u} (Fin (q + q) × Fin 1))))) := by sorry
