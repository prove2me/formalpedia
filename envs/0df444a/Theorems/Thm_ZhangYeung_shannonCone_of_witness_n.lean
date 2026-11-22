-- Prove2me | Theorems.Thm_ZhangYeung_shannonCone_of_witness_n
-- name    : ZhangYeung.shannonCone_of_witness_n
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:16.182353+00:00
-- url     : https://prove2.me/theorems/99b48662-a8a1-4943-bf6e-a5bb980247d7
-- title:
--   Zhang Yeung: shannon Cone of witness n
-- statement:
--   The lifted witness lies in `Γ_n`: each Shannon-cone axiom transports across
--   `Finset.preimage` via
--   `preimage_empty`, `monotone_preimage`, `preimage_union`, and `preimage_inter`, and then
--   reduces to
--   the base `shannonCone_of_witness`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L1065-L1083
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L1065-L1083

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem4
set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped Topology ZhangYeungPFR
universe u

theorem ZhangYeung.shannonCone_of_witness_n {n : ℕ} (hn : 4 ≤ n) :
    shannonConeN (FWitnessN hn) := by sorry
