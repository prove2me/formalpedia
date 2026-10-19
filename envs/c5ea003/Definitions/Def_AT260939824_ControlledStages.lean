-- Prove2me | Definitions.Def_AT260939824_ControlledStages
-- name    : AT260939824_ControlledStages
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:07:18.192886+00:00
-- url     : https://prove2.me/theorems/9a6349e4-28e9-4744-bd6d-0cb22c458f0a
-- title:
--   Equal-slot composition of deformation stages
-- statement:
--   Let $f:X\to Y$ be an initial map and let $H_n:Y\times[0,1]\to Y$ be deformation stages. Their endpoint states satisfy
--
--   $$ P_0=f,\qquad P_{n+1}(x)=H_n(P_n(x),1). $$
--
--   The stage-curve construction assigns equal time slots to the first $n$ stages. Its endpoint, seam, fixed-point, range, track, and joint-bound interfaces assemble finite sequences of controlled deformations without changing their actual intermediate states.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4–5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/ControlledStages.lean, selected declaration lines 17-19, 21-27, 29-37, 39-55, 57-67, 69-101, 103-115, 117-161, 185-197, 199-204, 206-218, 220-221, 223-236, 238-250; SHA-256 d0d28bed3a02f9beb35c8212925cc7d3c28ae611290bcb9d6dc8c71e2d418f5c. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

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

/-!
# Equal-slot concatenation of controlled deformation stages

The stages act on one ambient metric space. Their actual inputs are the
endpoints of the preceding stages. Equal slots give total track speed `N*D`,
while each finite concatenation has some finite joint Lipschitz constant.
-/

namespace AbelianTargets

open scoped NNReal unitInterval

noncomputable section

def stageState {X Y : Type*} (initial : X → Y) (stage : ℕ → Y × I → Y) : ℕ → X → Y
  | 0 => initial
  | n+1 => fun x => stage n (stageState initial stage n x,1)

def stageCurve {X Y : Type*} (initial : X → Y) (stage : ℕ → Y × I → Y) : ℕ → ℝ × X → Y
  | 0 => fun z => initial z.2
  | 1 => fun z => stage 0 (initial z.2,clampInterval z.1)
  | n+2 => fun z => if z.1 ≤ ((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ) then
      stageCurve initial stage (n+1) (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)*z.1,z.2)
    else stage (n+1) (stageState initial stage (n+1) z.2,
      clampInterval (((n+2 : ℕ) : ℝ)*z.1-((n+1 : ℕ) : ℝ)))

theorem stageCurve_zero {X Y : Type*} (initial : X → Y) (stage : ℕ → Y × I → Y)
    (hzero : ∀ n y, stage n (y,0)=y) (n : ℕ) (x : X) :
    stageCurve initial stage n (0,x)=initial x := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simpa [stageCurve] using hzero 0 (initial x)
  | more n ih ih' =>
    have hc : (0 : ℝ)≤((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ) := by positivity
    simpa only [stageCurve,if_pos hc,mul_zero] using ih'

theorem stageCurve_one {X Y : Type*} (initial : X → Y) (stage : ℕ → Y × I → Y)
    (n : ℕ) (x : X) : stageCurve initial stage n (1,x)=stageState initial stage n x := by
  rcases n with _ | n
  · rfl
  rcases n with _ | n
  · simp [stageCurve,stageState]
  · have hc : ¬(1 : ℝ)≤((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ) := by
      have hp : (0 : ℝ)<((n+2 : ℕ) : ℝ) := by positivity
      apply not_le.mpr
      apply (div_lt_one hp).2
      norm_cast; omega
    rw [stageCurve]
    dsimp only
    rw [if_neg hc]
    have ht : ((n+2 : ℕ) : ℝ)*1-((n+1 : ℕ) : ℝ)=1 := by push_cast; ring
    rw [ht,clampInterval_one]
    rfl

theorem stageCurve_seam {X Y : Type*} (initial : X → Y) (stage : ℕ → Y × I → Y)
    (hzero : ∀ n y, stage n (y,0)=y) (n : ℕ) (x : X) :
    stageCurve initial stage (n+1)
      ((((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))*(((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)),x)=
    stage (n+1) (stageState initial stage (n+1) x,
      clampInterval (((n+2 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))-((n+1 : ℕ) : ℝ))) := by
  have h₁ : (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))*(((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))=1 := by
    field_simp
  have h₂ : ((n+2 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))-((n+1 : ℕ) : ℝ)=0 := by
    field_simp; simp
  rw [h₁,h₂,clampInterval_zero,stageCurve_one,hzero]

theorem stageCurve_track {X Y : Type*} [MetricSpace Y]
    (initial : X → Y) (stage : ℕ → Y × I → Y)
    (hzero : ∀ n y, stage n (y,0)=y) (D : ℝ≥0)
    (htrack : ∀ n x, LipschitzWith D (fun t : I => stage n (stageState initial stage n x,t)))
    (n : ℕ) (x : X) : LipschitzWith ((n : ℝ≥0)*D) (fun t : ℝ => stageCurve initial stage n (t,x)) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [stageCurve] using (LipschitzWith.const (initial x) : LipschitzWith 0 (fun _ : ℝ => initial x))
  | one =>
    simpa only [Nat.cast_one,one_mul,stageCurve,stageState,Function.comp_def,mul_one] using
      (htrack 0 x).comp lipschitz_clampInterval
  | more n ih ih' =>
    let r : ℝ≥0 := ((n+2 : ℕ) : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
    have hr : |(((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))|≤r := by
      change |(((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))|≤((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)
      simp only [abs_of_nonneg (by positivity : (0 : ℝ)≤((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))]
      exact le_rfl
    have hf := ih'.comp (lipschitz_affine_le r
      (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)) 0 hr)
    have hconst : (((n+1 : ℕ) : ℝ≥0)*D)*r=((n+2 : ℕ) : ℝ≥0)*D := by
      dsimp [r]; field_simp
    rw [hconst] at hf
    have hg := ((htrack (n+1) x).comp lipschitz_clampInterval).comp
      (lipschitz_affine_le ((n+2 : ℕ) : ℝ≥0) ((n+2 : ℕ) : ℝ)
        (-((n+1 : ℕ) : ℝ)) (by
          change |((n+2 : ℕ) : ℝ)|≤((n+2 : ℕ) : ℝ)
          simp only [abs_of_nonneg (by positivity : (0 : ℝ)≤((n+2 : ℕ) : ℝ))]
          exact le_rfl))
    have hconst' : (D*1)*((n+2 : ℕ) : ℝ≥0)=((n+2 : ℕ) : ℝ≥0)*D := by ring
    rw [hconst'] at hg
    have he := lipschitz_glue_at _ _ hf hg
      (((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)) (by
        simpa only [Function.comp_def,add_zero,←sub_eq_add_neg] using stageCurve_seam initial stage hzero n x)
    simpa only [stageCurve,Function.comp_def,add_zero,sub_eq_add_neg] using he

theorem stageState_joint {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (initial : X → Y) (stage : ℕ → Y × I → Y)
    (hi : ∃ A : ℝ≥0, LipschitzWith A initial)
    (hs : ∀ n, ∃ J : ℝ≥0, LipschitzWith J (stage n)) (n : ℕ) :
    ∃ A : ℝ≥0, LipschitzWith A (stageState initial stage n) := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    obtain ⟨A,hA⟩ := ih
    obtain ⟨J,hJ⟩ := hs n
    refine ⟨J*max A 0, ?_⟩
    simpa only [stageState,Function.comp_def] using
      (hJ.comp (hA.prodMk (LipschitzWith.const (1 : I))))

theorem stageCurve_joint {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (initial : X → Y) (stage : ℕ → Y × I → Y)
    (hzero : ∀ n y, stage n (y,0)=y)
    (hi : ∃ A : ℝ≥0, LipschitzWith A initial)
    (hs : ∀ n, ∃ J : ℝ≥0, LipschitzWith J (stage n)) (n : ℕ) :
    ∃ J : ℝ≥0, LipschitzWith J (stageCurve initial stage n) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    obtain ⟨A,hA⟩ := hi
    exact ⟨A, by simpa [stageCurve] using hA.comp LipschitzWith.prod_snd⟩
  | one =>
    obtain ⟨A,hA⟩ := hi
    obtain ⟨J,hJ⟩ := hs 0
    refine ⟨J*max (A*1) (1*1), ?_⟩
    simpa only [stageCurve,Function.comp_def] using
      (hJ.comp ((hA.comp LipschitzWith.prod_snd).prodMk
        (lipschitz_clampInterval.comp LipschitzWith.prod_fst)))
  | more n ih ih' =>
    obtain ⟨A,hA⟩ := ih'
    obtain ⟨B,hB⟩ := stageState_joint initial stage hi hs (n+1)
    obtain ⟨J,hJ⟩ := hs (n+1)
    let r : ℝ≥0 := ((n+2 : ℕ) : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
    have hr : |(((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))|≤r := by
      change |(((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))|≤((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)
      rw [abs_of_nonneg (by positivity)]
    have hp := ((lipschitz_affine_le r
      (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)) 0 hr).comp
      (LipschitzWith.prod_fst : LipschitzWith 1 (Prod.fst : ℝ × X → ℝ))).prodMk
      (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × X → X))
    have hf := hA.comp hp
    have ht := (lipschitz_clampInterval.comp
      (lipschitz_affine_le ((n+2 : ℕ) : ℝ≥0) ((n+2 : ℕ) : ℝ)
        (-((n+1 : ℕ) : ℝ)) (by
          change |((n+2 : ℕ) : ℝ)|≤((n+2 : ℕ) : ℝ)
          rw [abs_of_nonneg (by positivity)]))).comp
      (LipschitzWith.prod_fst : LipschitzWith 1 (Prod.fst : ℝ × X → ℝ))
    have hg := hJ.comp ((hB.comp LipschitzWith.prod_snd).prodMk ht)
    let K := max (A*max (r*1) 1) (J*max (B*1) ((1*((n+2 : ℕ) : ℝ≥0))*1))
    refine ⟨2*K, ?_⟩
    have hglue := lipschitz_glue_product_at _ _
      (hf.weaken (le_max_left _ _)) (hg.weaken (le_max_right _ _))
      (((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)) (fun x => by
        simpa only [Function.comp_def,add_zero,←sub_eq_add_neg] using
          stageCurve_seam initial stage hzero n x)
    simpa only [stageCurve,Function.comp_def,add_zero,sub_eq_add_neg] using hglue





theorem stageCurve_mem_of_tracks {X Y : Type*} (initial : X → Y) (stage : ℕ → Y × I → Y)
    (S : Set Y) (hi : ∀ x, initial x ∈ S)
    (hs : ∀ n x t, stage n (stageState initial stage n x,t) ∈ S)
    (n : ℕ) (z : ℝ × X) : stageCurve initial stage n z ∈ S := by
  induction n using Nat.twoStepInduction generalizing z with
  | zero => exact hi z.2
  | one => exact hs 0 z.2 _
  | more n ih ih' =>
    rw [stageCurve]
    dsimp only
    split_ifs
    · exact ih' _
    · exact hs (n+1) z.2 _

theorem stageState_fixed {X Y : Type*} (initial : X → Y) (stage : ℕ → Y × I → Y)
    (x : X) (b : Y) (hi : initial x=b) (hs : ∀ n t, stage n (b,t)=b) (n : ℕ) :
    stageState initial stage n x=b := by
  induction n with
  | zero => exact hi
  | succ n ih => simpa only [stageState,ih] using hs n 1

theorem stageCurve_fixed {X Y : Type*} (initial : X → Y) (stage : ℕ → Y × I → Y)
    (x : X) (b : Y) (hi : initial x=b) (hs : ∀ n t, stage n (b,t)=b)
    (n : ℕ) (t : ℝ) : stageCurve initial stage n (t,x)=b := by
  induction n using Nat.twoStepInduction generalizing t with
  | zero => exact hi
  | one => simpa only [stageCurve,hi] using hs 0 (clampInterval t)
  | more n ih ih' =>
    rw [stageCurve]
    dsimp only
    split_ifs
    · exact ih' _
    · rw [stageState_fixed initial stage x b hi hs]
      exact hs _ _

def stageHomotopy {X Y : Type*} (initial : X → Y) (stage : ℕ → Y × I → Y)
    (n : ℕ) (z : X × I) : Y := stageCurve initial stage n ((z.2 : ℝ),z.1)

theorem stageHomotopy_joint {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (initial : X → Y) (stage : ℕ → Y × I → Y)
    (hzero : ∀ n y, stage n (y,0)=y)
    (hi : ∃ A : ℝ≥0, LipschitzWith A initial)
    (hs : ∀ n, ∃ J : ℝ≥0, LipschitzWith J (stage n)) (n : ℕ) :
    ∃ J : ℝ≥0, LipschitzWith J (stageHomotopy initial stage n) := by
  obtain ⟨J,hJ⟩ := stageCurve_joint initial stage hzero hi hs n
  have he : LipschitzWith 1 (fun z : X × I => ((z.2 : ℝ),z.1)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change max (dist x.2 y.2) (dist x.1 y.1) ≤ (1 : ℝ)*max (dist x.1 y.1) (dist x.2 y.2)
    simp only [one_mul,max_comm]
    exact le_rfl
  exact ⟨J, by simpa only [stageHomotopy,Function.comp_def,mul_one] using hJ.comp he⟩

theorem stageHomotopy_track {X Y : Type*} [MetricSpace Y]
    (initial : X → Y) (stage : ℕ → Y × I → Y)
    (hzero : ∀ n y, stage n (y,0)=y) (D : ℝ≥0)
    (htrack : ∀ n x, LipschitzWith D (fun t : I => stage n (stageState initial stage n x,t)))
    (n : ℕ) (x : X) :
    LipschitzWith ((n : ℝ≥0)*D) (fun t : I => stageHomotopy initial stage n (x,t)) := by
  have he : LipschitzWith 1 ((↑) : I → ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist x y ≤ (1 : ℝ)*dist x y
    simp
  simpa only [stageHomotopy,Function.comp_def,mul_one] using
    (stageCurve_track initial stage hzero D htrack n x).comp he

end

end AbelianTargets


