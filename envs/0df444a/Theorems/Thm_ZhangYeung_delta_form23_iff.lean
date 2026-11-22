-- Prove2me | Theorems.Thm_ZhangYeung_delta_form23_iff
-- name    : ZhangYeung.delta_form23_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:53:20.51742+00:00
-- url     : https://prove2.me/theorems/aa4a5a6a-976e-4e68-9ebd-f31d381d83d3
-- title:
--   Zhang Yeung: delta form23 iff
-- statement:
--   The integer-scaled conclusion of `delta_form23_of_form21_form22` is equivalent to the
--   paper's `1/2`
--   and `1/4` statement [@zhangyeung1998, §III, eq. 23].
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L191-L198
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L191-L198

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

theorem ZhangYeung.delta_form23_iff
    (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    4 * delta Z U X Y μ
        ≤ 2 * I[X : Y; μ] + I[X : ⟨Z, U⟩; μ] + I[Y : ⟨Z, U⟩; μ]
      ↔ delta Z U X Y μ
          ≤ (1 / 2) * I[X : Y; μ] + (1 / 4) * (I[X : ⟨Z, U⟩; μ] + I[Y : ⟨Z,
            U⟩; μ]) := by sorry
