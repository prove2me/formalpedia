-- Prove2me | Definitions.Def_fta_winding_infra
-- name    : fta_winding_infra
-- status  : Definition
-- author  : @Henry Yuen
-- created : 2026-05-22T14:58:43.063721+00:00
-- url     : https://prove2.me/theorems/53daaab6-fde4-4d17-a0ca-a6e329c38c33
-- statement:
--   Reusable circle-lift and boundary-loop infrastructure for a winding-number proof of the Fundamental Theorem of Algebra.
-- source:
--   https://prove2me.vercel.app

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Algebra.Polynomial.EraseLead

noncomputable section

open scoped unitInterval
open Complex Polynomial

abbrev FtaCircle : Type := AddCircle (2 * Real.pi)

def FtaHasLift (γ : FtaCircle → Circle) : Prop :=
  ∃ Γ : FtaCircle → ℝ, Continuous Γ ∧ ∀ θ : FtaCircle, Circle.exp (Γ θ) = γ θ

def FtaCircleHomotopic (γ δ : FtaCircle → Circle) : Prop :=
  ∃ H : C(I × FtaCircle, Circle),
    (∀ θ : FtaCircle, H (0, θ) = γ θ) ∧
    (∀ θ : FtaCircle, H (1, θ) = δ θ)

noncomputable def FtaNormalize (z : ℂ) : Circle :=
  if hz : z = 0 then 1 else
    ⟨z / (‖z‖ : ℂ), by
      simp [Submonoid.unitSphere, norm_ne_zero_iff.mpr hz]⟩

def FtaBoundaryPoint (R : ℝ) (θ : FtaCircle) : ℂ :=
  (R : ℂ) * (AddCircle.homeomorphCircle' θ : ℂ)

def FtaLeadingTermBoundary (f : ℂ[X]) (R : ℝ) (θ : FtaCircle) : ℂ :=
  f.leadingCoeff * (FtaBoundaryPoint R θ) ^ f.natDegree

noncomputable def FtaBoundaryLoop (f : ℂ[X]) (R : ℝ) : FtaCircle → Circle :=
  fun θ : FtaCircle => FtaNormalize (f.eval (FtaBoundaryPoint R θ))

noncomputable def FtaLeadingLoop (u : Circle) (n : ℕ) : FtaCircle → Circle :=
  fun θ : FtaCircle => u * (AddCircle.homeomorphCircle' θ) ^ n

noncomputable def FtaLeadingCoeffCircle (f : ℂ[X]) : Circle :=
  FtaNormalize f.leadingCoeff

def FtaClosedDiskRootless (f : ℂ[X]) (R : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ R → ¬ f.IsRoot z

def FtaBoundaryNonzero (f : ℂ[X]) (R : ℝ) : Prop :=
  ∀ θ : FtaCircle, f.eval (FtaBoundaryPoint R θ) ≠ 0

def FtaStraightLineNonzero (a b : ℂ) : Prop :=
  ∀ t : I, ((1 - (t : ℝ) : ℂ) * a + ((t : ℝ) : ℂ) * b) ≠ 0

def FtaLeadingDominatesOnBoundary (f : ℂ[X]) (R : ℝ) : Prop :=
  FtaBoundaryNonzero f R ∧
    ∀ θ : FtaCircle,
      FtaStraightLineNonzero (f.eval (FtaBoundaryPoint R θ)) (FtaLeadingTermBoundary f R θ)


