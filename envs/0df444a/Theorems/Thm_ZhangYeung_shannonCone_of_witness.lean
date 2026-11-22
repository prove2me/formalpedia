-- Prove2me | Theorems.Thm_ZhangYeung_shannonCone_of_witness
-- name    : ZhangYeung.shannonCone_of_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:00.701978+00:00
-- url     : https://prove2.me/theorems/505a22aa-6816-43f6-b025-d17a24a02ad0
-- title:
--   Zhang Yeung: shannon Cone of witness
-- statement:
--   Part (a) of Theorem 4: the witness satisfies the three Shannon-cone axioms (paper eq.
--   11). The
--   empty-set and monotonicity checks close by finite `decide` over the `ℚ`-valued witness,
--   while
--   submodularity is proved structurally by decomposing the witness into a cardinality
--   profile plus one
--   exceptional pair bonus.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L494-L509
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L494-L509

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

theorem ZhangYeung.shannonCone_of_witness : shannonCone FWitness := by sorry
