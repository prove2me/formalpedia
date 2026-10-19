-- Prove2me | Definitions.Def_AT260939824_CurveFamilyStages
-- name    : AT260939824_CurveFamilyStages
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:08:20.468525+00:00
-- url     : https://prove2.me/theorems/2ff606fa-e9df-4339-8692-a5ae21474b89
-- title:
--   Equal-slot families of curves
-- statement:
--   Given sets $X,Y$ and curves $H_n:X\times[0,1]\to Y$ indexed by natural numbers $n$, this bundle defines their finite equal-slot assembly and the corresponding unit-interval reparametrization. The seam convention records the literal terminal value of the last curve. These operations let a finite sequence of deformations be treated as one parametrized family.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/CurveFamilyStages.lean, selected declaration lines 8-13, 15-22, 24-37, 125-133, 135-136; SHA-256 90bffa2ab1a52975c548436151b65b89efbd876cc18f62f75a0e1c6f8691283c. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_RelativePathContraction
import Init
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/-! Equal-slot concatenation of a family of curves with literal seams. -/
namespace AbelianTargets
open scoped NNReal unitInterval
noncomputable section

def familyCurve {X Y : Type*} (H : ℕ → X × I → Y) : ℕ → ℝ × X → Y
  | 0 => fun z => H 0 (z.2,0)
  | 1 => fun z => H 0 (z.2,clampInterval z.1)
  | n+2 => fun z => if z.1 ≤ ((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ) then
      familyCurve H (n+1) (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)*z.1,z.2)
    else H (n+1) (z.2,clampInterval (((n+2 : ℕ) : ℝ)*z.1-((n+1 : ℕ) : ℝ)))

theorem familyCurve_zero {X Y : Type*} (H : ℕ → X × I → Y) (n : ℕ) (x : X) :
    familyCurve H n (0,x)=H 0 (x,0) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [familyCurve]
  | more n ih ih' =>
    have hc : (0 : ℝ)≤((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ) := by positivity
    simpa only [familyCurve,if_pos hc,mul_zero] using ih'

theorem familyCurve_one {X Y : Type*} (H : ℕ → X × I → Y) (n : ℕ) (x : X) :
    familyCurve H (n+1) (1,x)=H n (x,1) := by
  cases n with
  | zero => simp [familyCurve]
  | succ n =>
    have hc : ¬(1 : ℝ)≤((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ) := by
      apply not_le.mpr
      apply (div_lt_one (by positivity)).2
      norm_cast; omega
    rw [familyCurve]
    dsimp only
    rw [if_neg hc]
    have ht : ((n+2 : ℕ) : ℝ)*1-((n+1 : ℕ) : ℝ)=1 := by push_cast; ring
    rw [ht,clampInterval_one]









theorem familyCurve_fixed {X Y : Type*} (H : ℕ → X × I → Y) (x : X) (b : Y)
    (hfix : ∀ n t, H n (x,t)=b) (n : ℕ) (t : ℝ) : familyCurve H n (t,x)=b := by
  induction n using Nat.twoStepInduction generalizing t with
  | zero => exact hfix 0 0
  | one => exact hfix 0 _
  | more n ih ih' =>
    rw [familyCurve]; dsimp only; split_ifs
    · exact ih' _
    · exact hfix (n+1) _

def familyHomotopy {X Y : Type*} (H : ℕ → X × I → Y) (n : ℕ) (z : X × I) : Y :=
  familyCurve H n ((z.2 : ℝ),z.1)





end
end AbelianTargets


