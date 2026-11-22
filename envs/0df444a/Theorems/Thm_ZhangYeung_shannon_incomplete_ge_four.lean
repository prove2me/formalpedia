-- Prove2me | Theorems.Thm_ZhangYeung_shannon_incomplete_ge_four
-- name    : ZhangYeung.shannon_incomplete_ge_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:02:44.20466+00:00
-- url     : https://prove2.me/theorems/2baa943b-b765-460a-becf-2251bc8d375d
-- title:
--   Zhang Yeung: shannon incomplete ge four
-- statement:
--   Stronger cone-level corollary for `n ≥ 4`: the lifted witness separates `Γ_n` from the
--   `Fin
--   n`-indexed Zhang-Yeung cone. Since `closure (Γ_n^*) ⊆ tildeΓ_n`, this strictly
--   strengthens the
--   exact paper-level theorem `theorem4_ge_four`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L1146-L1148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L1146-L1148

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

theorem ZhangYeung.shannon_incomplete_ge_four (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : Finset (Fin n) → ℝ, shannonConeN F ∧ ¬ zhangYeungHoldsN F := by sorry
