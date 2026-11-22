-- Prove2me | Theorems.Thm_ZhangYeung_delta_of_condMI_vanishes_eq
-- name    : ZhangYeung.delta_of_condMI_vanishes_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:53:04.084795+00:00
-- url     : https://prove2.me/theorems/832fb66d-2a46-41ea-96d8-22cc9b2334b8
-- title:
--   Zhang Yeung: delta of cond MI vanishes eq
-- statement:
--   **Lemma 2 (abstract form) of [@zhangyeung1998, §III, eq. 45].** For any four
--   discrete random
--   variables `A, B, C, D` on a probability space `(Ω, ν)` with `I[A : D | ⟨B, C⟩; ν] = 0`,
--
--     `Δ(B, C | A, D) = I[A : D] - I[A : D | B] - I[A : D | C] - I[B : C | ⟨A, D⟩]`.
--
--   This is the paper's eq. (45) abstracted away from the copy construction: the identity
--   holds
--   whenever one conditional mutual information vanishes. The three subtracted conditional
--   mutual
--   informations on the right are each nonnegative, so this identity immediately implies the
--   paper's
--   inequality form `Δ(B, C | A, D) ≤ I[A : D]` via `linarith`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean#L199-L231
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean#L199-L231

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u

theorem ZhangYeung.delta_of_condMI_vanishes_eq
    {Ω : Type*} [MeasurableSpace Ω]
    {α β γ δ : Type*}
    [Finite α] [Finite β] [Finite γ] [Finite δ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] [MeasurableSingletonClass δ]
    {A : Ω → α} {B : Ω → β} {C : Ω → γ} {D : Ω → δ}
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (hVanish : I[A : D|⟨B, C⟩;ν] = 0) :
    delta B C A D ν
      = I[A : D; ν] - I[A : D | B; ν] - I[A : D | C; ν]
        - I[B : C | ⟨A, D⟩; ν] := by sorry
