-- Prove2me | Theorems.Thm_ZhangYeung_delta_form21_iff
-- name    : ZhangYeung.delta_form21_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:55:36.5155+00:00
-- url     : https://prove2.me/theorems/86199d83-16b6-42de-8fd5-e121c4553540
-- title:
--   Zhang Yeung: delta form21 iff
-- statement:
--   Paper eq. (21) of [@zhangyeung1998, §III]: the inequality `2·Δ(Z, U | X, Y) ≤ I(X;Y) +
--   I(X;ZU) +
--   I(Z;U|X) - I(Z;U|Y)` is equivalent to the compact form `2·I(Z;U) - 3·I(Z;U|X) - I(Z;U|Y)
--   ≤ I(X;Y) +
--   I(X;ZU)`, which is the shape a copy-lemma proof naturally produces.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L146-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L146-L152

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]

theorem ZhangYeung.delta_form21_iff
    (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    2 * delta Z U X Y μ
        ≤ I[X : Y; μ] + I[X : ⟨Z, U⟩; μ] + I[Z : U | X; μ] - I[Z : U | Y; μ]
      ↔ 2 * I[Z : U; μ] - 3 * I[Z : U | X; μ] - I[Z : U | Y; μ]
          ≤ I[X : Y; μ] + I[X : ⟨Z, U⟩; μ] := by sorry
