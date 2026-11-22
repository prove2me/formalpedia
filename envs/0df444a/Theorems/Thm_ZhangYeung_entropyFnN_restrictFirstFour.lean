-- Prove2me | Theorems.Thm_ZhangYeung_entropyFnN_restrictFirstFour
-- name    : ZhangYeung.entropyFnN_restrictFirstFour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:01:31.971965+00:00
-- url     : https://prove2.me/theorems/4cfd2671-8cb9-49b7-ae04-8f81f82a4fef
-- title:
--   Zhang Yeung: entropy Fn N restrict First Four
-- statement:
--   Restricting an `n`-variable entropy function to the first four coordinates agrees with
--   taking the
--   entropy function of the restricted family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/EntropyRegion.lean#L148-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/EntropyRegion.lean#L148-L176

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped Topology
universe u

theorem ZhangYeung.entropyFnN_restrictFirstFour
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {S : Fin n → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    {X : ∀ i : Fin n, Ω → S i} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) (hn : 4 ≤ n) :
    restrictFirstFour hn (entropyFnN X μ) =
      entropyFnN (fun i : Fin 4 => X (Fin.castLE hn i)) μ := by sorry
