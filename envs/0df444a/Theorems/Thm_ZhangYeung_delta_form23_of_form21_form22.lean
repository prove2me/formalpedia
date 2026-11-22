-- Prove2me | Theorems.Thm_ZhangYeung_delta_form23_of_form21_form22
-- name    : ZhangYeung.delta_form23_of_form21_form22
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:53:11.377804+00:00
-- url     : https://prove2.me/theorems/aa26a9c4-0b91-4d6d-a868-665b2e8fcc3d
-- title:
--   Zhang Yeung: delta form23 of form21 form22
-- statement:
--   Paper eq. (23) of [@zhangyeung1998, §III], the symmetric form of Theorem 3, follows from
--   eqs. (21)
--   and (22) by averaging. This lemma contains no measure-theoretic content; the
--   inequalities (21) and
--   (22) are the nontrivial inputs and are proved in a later milestone via the copy lemma.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L172-L184
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L172-L184

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

theorem ZhangYeung.delta_form23_of_form21_form22
    {Z : Ω → S₁} {U : Ω → S₂} {X : Ω → S₃} {Y : Ω → S₄} {μ : Measure Ω}
    (h21 : 2 * delta Z U X Y μ
        ≤ mutualInfo X Y μ + mutualInfo X (fun ω => (Z ω, U ω)) μ
          + I[Z : U|X;μ] - I[Z : U|Y;μ])
    (h22 : 2 * delta Z U X Y μ
        ≤ mutualInfo X Y μ + mutualInfo Y (fun ω => (Z ω, U ω)) μ
          - I[Z : U|X;μ] + I[Z : U|Y;μ]) :
    4 * delta Z U X Y μ
      ≤ 2 * mutualInfo X Y μ
        + mutualInfo X (fun ω => (Z ω, U ω)) μ
        + mutualInfo Y (fun ω => (Z ω, U ω)) μ := by sorry
