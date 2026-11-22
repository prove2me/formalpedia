-- Prove2me | Theorems.Thm_ZhangYeung_zhangYeungHolds_of_tendsto
-- name    : ZhangYeung.zhangYeungHolds_of_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:56:33.068623+00:00
-- url     : https://prove2.me/theorems/6eda4f55-2f3b-4eeb-be8e-39576d6a01cf
-- title:
--   Zhang Yeung: zhang Yeung Holds of tendsto
-- statement:
--   `zhangYeungHolds` is closed under pointwise convergence: if each `F_seq k` lies in
--   `tildeΓ_4` and
--   `F_seq k α → F α` pointwise, then `F` lies in `tildeΓ_4` too. The inequality
--   `zhangYeungAt F` is a
--   finite `≤` between continuous linear combinations of coordinate evaluations, hence
--   preserved under
--   pointwise limits.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L905-L926
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L905-L926

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

theorem ZhangYeung.zhangYeungHolds_of_tendsto
    {F_seq : ℕ → Finset (Fin 4) → ℝ} {F : Finset (Fin 4) → ℝ}
    (h_seq : ∀ k, zhangYeungHolds (F_seq k))
    (h_lim : ∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α))) :
    zhangYeungHolds F := by sorry
