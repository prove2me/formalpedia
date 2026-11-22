-- Prove2me | Theorems.Thm_ZhangYeung_theorem5
-- name    : ZhangYeung.theorem5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:56:42.247808+00:00
-- url     : https://prove2.me/theorems/6001b318-aaa8-4553-9da9-3bf46203727e
-- title:
--   Zhang Yeung: theorem5
-- statement:
--   **Theorem 5 of [@zhangyeung1998, §III, eq. 27]** -- the `n + 2`-variable Zhang-Yeung
--   inequality,
--   indexed by a distinguished coordinate `i : Fin n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem5.lean#L265-L388
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem5.lean#L265-L388

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem5
set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u
variable {Ω : Type*} [MeasurableSpace Ω]
  {n : ℕ}
  {S_U S_Z : Type u} {S : Fin n → Type u}
  [MeasurableSpace S_U] [MeasurableSpace S_Z]
  [∀ i, MeasurableSpace (S i)]
  [Finite S_U] [Finite S_Z] [∀ i, Finite (S i)]
  [MeasurableSingletonClass S_U] [MeasurableSingletonClass S_Z]
  [∀ i, MeasurableSingletonClass (S i)]

theorem ZhangYeung.theorem5
    {U : Ω → S_U} {Z : Ω → S_Z} {X : ∀ i : Fin n, Ω → S i}
    (hU : Measurable U) (hZ : Measurable Z) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : Fin n) :
    2 ≤ n →
    n * I[U : Z; μ] - ∑ j, I[U : Z | X j; μ] - n * I[U : Z | X i; μ]
      ≤ I[X i : ⟨U, Z⟩; μ]
        + ∑ j, H[X j; μ]
        - H[(fun ω : Ω => fun j : Fin n => X j ω); μ] := by sorry
