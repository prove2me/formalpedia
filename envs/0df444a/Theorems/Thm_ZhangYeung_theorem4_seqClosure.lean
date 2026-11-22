-- Prove2me | Theorems.Thm_ZhangYeung_theorem4_seqClosure
-- name    : ZhangYeung.theorem4_seqClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:02:32.294735+00:00
-- url     : https://prove2.me/theorems/8297dee4-2d39-48e1-b1f3-122e03a845b4
-- title:
--   Zhang Yeung: theorem4 seq Closure
-- statement:
--   Sequence-level strengthening of the witness exclusion: `FWitness` is not the pointwise
--   limit of
--   any sequence of set functions in `tildeΓ_4`. This auxiliary is stronger than `theorem4`,
--   but it is
--   phrased in the larger Zhang-Yeung cone rather than in `closure (Γ_4^*)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L1023-L1031
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L1023-L1031

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

theorem ZhangYeung.theorem4_seqClosure :
    ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧
      ∀ (F_seq : ℕ → Finset (Fin 4) → ℝ),
        (∀ k, zhangYeungHolds (F_seq k)) →
        (∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α))) →
        False := by sorry
