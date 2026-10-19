-- Prove2me | solution 1 for AbelianTargets.familyCurve_joint
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:03:44.428983+00:00
-- url     : https://prove2.me/submissions/bc3561b0-65aa-4568-8e4f-fccb63b3bd9b

import Definitions.Def_AT260939824_CurveFamilyStages
import Definitions.Def_AT260939824_JointHomotopyGluing
import Definitions.Def_AT260939824_RelativePathBounds
import Definitions.Def_AT260939824_RelativePathContraction
import Init
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.CurveFamilyStages
section
/-! Equal-slot concatenation of a family of curves with literal seams. -/
namespace AbelianTargets
open scoped NNReal unitInterval
noncomputable section







theorem familyCurve_seam {X Y : Type*} (H : ℕ → X × I → Y)
    (hseam : ∀ n x, H n (x,1)=H (n+1) (x,0)) (n : ℕ) (x : X) :
    familyCurve H (n+1)
      ((((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))*(((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)),x)=
    H (n+1) (x,clampInterval (((n+2 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))-((n+1 : ℕ) : ℝ))) := by
  have h₁ : (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))*(((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))=1 := by field_simp
  have h₂ : ((n+2 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))-((n+1 : ℕ) : ℝ)=0 := by field_simp; simp
  rw [h₁,h₂,clampInterval_zero,familyCurve_one,hseam]















end
end AbelianTargets

end

/-! Equal-slot concatenation of a family of curves with literal seams. -/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open scoped NNReal unitInterval

theorem solution {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (H : ℕ → X × I → Y) (hseam : ∀ n x, H n (x,1)=H (n+1) (x,0))
    (hjoint : ∀ n, ∃ J : ℝ≥0, LipschitzWith J (H n)) (n : ℕ) :
    ∃ J : ℝ≥0, LipschitzWith J (familyCurve H n) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    obtain ⟨J,hJ⟩ := hjoint 0
    refine ⟨J*max 1 0,?_⟩
    simpa only [familyCurve,Function.comp_def] using
      hJ.comp ((LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × X → X)).prodMk
        (LipschitzWith.const (0 : I)))
  | one =>
    obtain ⟨J,hJ⟩ := hjoint 0
    refine ⟨J*max 1 (1*1),?_⟩
    simpa only [familyCurve,Function.comp_def] using
      hJ.comp ((LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × X → X)).prodMk
        (lipschitz_clampInterval.comp LipschitzWith.prod_fst))
  | more n ih ih' =>
    obtain ⟨A,hA⟩ := ih'
    obtain ⟨J,hJ⟩ := hjoint (n+1)
    let r : ℝ≥0 := ((n+2 : ℕ) : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
    have hr : |(((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))|≤r := by
      change |(((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))|≤((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)
      rw [abs_of_nonneg (by positivity)]
    have hp := ((lipschitz_affine_le r (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)) 0 hr).comp
      (LipschitzWith.prod_fst : LipschitzWith 1 (Prod.fst : ℝ × X → ℝ))).prodMk
      (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × X → X))
    have hf := hA.comp hp
    have ht := (lipschitz_clampInterval.comp
      (lipschitz_affine_le ((n+2 : ℕ) : ℝ≥0) ((n+2 : ℕ) : ℝ) (-((n+1 : ℕ) : ℝ)) (by
        change |((n+2 : ℕ) : ℝ)|≤((n+2 : ℕ) : ℝ)
        rw [abs_of_nonneg (by positivity)]))).comp
      (LipschitzWith.prod_fst : LipschitzWith 1 (Prod.fst : ℝ × X → ℝ))
    have hg := hJ.comp ((LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × X → X)).prodMk ht)
    let K := max (A*max (r*1) 1) (J*max 1 ((1*((n+2 : ℕ) : ℝ≥0))*1))
    refine ⟨2*K,?_⟩
    have hglue := lipschitz_glue_product_at _ _ (hf.weaken (le_max_left _ _)) (hg.weaken (le_max_right _ _))
      (((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)) (fun x => by
        simpa only [Function.comp_def,add_zero,←sub_eq_add_neg] using familyCurve_seam H hseam n x)
    simpa only [familyCurve,Function.comp_def,add_zero,sub_eq_add_neg] using hglue
