-- Prove2me | Theorems.Thm_ZhangYeung_theorem2
-- name    : ZhangYeung.theorem2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:01:53.397082+00:00
-- url     : https://prove2.me/theorems/846aced8-5324-4140-b972-c333523f9bb1
-- title:
--   Zhang Yeung: theorem2
-- statement:
--   **Zhang-Yeung Theorem 2** ([@zhangyeung1998], eqs. 16-17; proved in
--   [@zhangyeung1997, Theorem
--   3]). For any four discrete random variables `X, Y, Z, U` on a probability space, if `I[X
--   : Y; μ] =
--   0` and `I[X : Y | Z; μ] = 0`, then `I[X : Y | ⟨Z, U⟩; μ] ≤ I[Z : U | ⟨X, Y⟩; μ] + I[X :
--   Y | U;
--   μ]`.
--
--   The proof factors into a Shannon-algebra reduction (`theorem2_shannon_identity`) that
--   isolates the
--   non-Shannon-type core `Δ(Z, U | X, Y) ≤ 0` via the `ZhangYeung.delta` quantity from M1,
--   and the
--   [@zhangyeung1997] KL-divergence argument (`theorem2_delta_le_zero`) that discharges that
--   core.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem2.lean#L2080-L2091
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem2.lean#L2080-L2091

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Analysis_SpecialFunctions_NegMulLog
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem2
set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory Real
open scoped ZhangYeungPFR
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
omit [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]

theorem ZhangYeung.theorem2
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : mutualInfo X Y μ = 0)
    (h₂ : I[X : Y|Z;μ] = 0) :
    I[X : Y | ⟨Z, U⟩; μ] ≤ I[Z : U | ⟨X, Y⟩; μ] + I[X : Y | U; μ] := by sorry
