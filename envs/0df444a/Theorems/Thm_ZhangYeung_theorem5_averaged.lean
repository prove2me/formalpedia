-- Prove2me | Theorems.Thm_ZhangYeung_theorem5_averaged
-- name    : ZhangYeung.theorem5_averaged
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:02:54.705816+00:00
-- url     : https://prove2.me/theorems/75606575-a63d-4db1-aba9-96238d9f3c00
-- title:
--   Zhang Yeung: theorem5 averaged
-- statement:
--   **Theorem 5 of [@zhangyeung1998, §III, eq. 28]** -- the averaged symmetric form of the
--   `n +
--   2`-variable Zhang-Yeung inequality.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem5.lean#L395-L451
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem5.lean#L395-L451

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

theorem ZhangYeung.theorem5_averaged
    (hn : 2 ≤ n)
    {U : Ω → S_U} {Z : Ω → S_Z} {X : ∀ i : Fin n, Ω → S i}
    (hU : Measurable U) (hZ : Measurable Z) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    n * I[U : Z; μ] - 2 * (∑ j, I[U : Z | X j; μ])
      ≤ (1 / n : ℝ) * (∑ i, I[X i : ⟨U, Z⟩; μ])
        + ∑ j, H[X j; μ]
        - H[(fun ω : Ω => fun j : Fin n => X j ω); μ] := by sorry
