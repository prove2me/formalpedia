-- Prove2me | solution 1 for Erdos390.WholePaper.tangentOrderedPairEndpointBudget_div_le_charges_of_equationBounds_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:52:06.782427+00:00
-- url     : https://prove2.me/submissions/e7c5b95e-2fdf-4cf5-a3ba-97b7e0d4e024

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_007

/- Source module: Erdos390.WholePaper.TangentPairArithmetic -/
section


/-!
# Finite arithmetic for tangent collision pairs

This file discharges the finite four-endpoint part of the
`hpairArithmetic` contract in `TangentSplitRequestLoads`.  It separates two
layers.

* Four per-equation bounds are assembled into the paper's one disjoint charge
  and two possible shared-label charges.  Distinct endpoints on the right
  request ensure that each left label can create at most one shared equation.
* A paper-scale specialization derives the per-equation bounds from a supplied
  effective list-density inequality

  `density * n <= lowerCard(request) * endpointLabel(request, side)`.

The specialization uses only `tangentBroadUpper n K h <= 2*n`, prime-label
positivity, and explicit hypotheses saying that every endpoint is at most a
cutoff whose first and second powers are at most `n`.  It yields the concrete
coefficients `12 / density^2` and `3 / density^2`.

No clean-list density estimate or cutoff asymptotic is proved here.  In a
paper application those are precisely the inputs needed to establish the
displayed effective-density and cutoff inequalities.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Coefficients and elementary endpoint budgets -/















/-! ## Assembly of four endpoint equations -/

private theorem sum_endpointLabel_eq_sharedCharge
    {Request : Type*} (source target : Request → ℕ)
    (request : Request) (label : ℕ) (charge : ℝ)
    (hendpointDistinct : source request ≠ target request) :
    (∑ side : TangentEndpointSide,
        if label = tangentEndpointLabel source target side request
        then charge else 0) =
      if tangentRequestHasLabel source target label request
      then charge else 0 := by
  classical
  rw [show (Finset.univ : Finset TangentEndpointSide) =
    {.source, .target} by decide]
  by_cases hsource : source request = label
  · subst label
    have htarget : target request ≠ source request :=
      Ne.symm hendpointDistinct
    simp [tangentEndpointLabel, tangentRequestHasLabel,
      hendpointDistinct, htarget]
  · by_cases htarget : target request = label
    · subst label
      have hsource' : target request ≠ source request := Ne.symm hsource
      simp [tangentEndpointLabel, tangentRequestHasLabel,
        hsource, hsource']
    · have hsource' : label ≠ source request := fun h ↦ hsource h.symm
      have htarget' : label ≠ target request := fun h ↦ htarget h.symm
      simp [tangentEndpointLabel, tangentRequestHasLabel,
        hsource, htarget, hsource', htarget']

/-- Four per-equation bounds, each paying one quarter of the disjoint charge,
assemble into exactly the disjoint/shared expression required by the load
terminal. -/
theorem tangentOrderedPairEndpointBudget_div_le_charges_of_equationBounds
    {Request : Type*} [DecidableEq Request]
    (N : ℕ) (source target : Request → ℕ)
    (lowerCard : Request → ℕ)
    (disjointCharge : ℝ) (sharedCharge : ℕ → ℝ)
    (hendpointDistinct : ∀ request, source request ≠ target request)
    (hEquation : ∀ left right,
      ∀ leftSide rightSide : TangentEndpointSide,
      (tangentEndpointEquationBudget N
          (tangentEndpointLabel source target leftSide left)
          (tangentEndpointLabel source target rightSide right) : ℝ) /
          (lowerCard left * lowerCard right) ≤
        disjointCharge / 4 +
          (if tangentEndpointLabel source target leftSide left =
              tangentEndpointLabel source target rightSide right
            then sharedCharge
              (tangentEndpointLabel source target leftSide left)
            else 0))
    (left right : Request) :
    (tangentOrderedPairEndpointBudget N source target left right : ℝ) /
        (lowerCard left * lowerCard right) ≤
      disjointCharge +
        (if tangentRequestHasLabel source target (source left) right
          then sharedCharge (source left) else 0) +
        (if tangentRequestHasLabel source target (target left) right
          then sharedCharge (target left) else 0) := by
  classical
  let denominator : ℝ := lowerCard left * lowerCard right
  have hcast :
      (tangentOrderedPairEndpointBudget N source target left right : ℝ) =
        ∑ leftSide : TangentEndpointSide,
          ∑ rightSide : TangentEndpointSide,
            (tangentEndpointEquationBudget N
              (tangentEndpointLabel source target leftSide left)
              (tangentEndpointLabel source target rightSide right) : ℝ) := by
    simp only [tangentOrderedPairEndpointBudget, Nat.cast_sum]
  have huniv : (Finset.univ : Finset TangentEndpointSide) =
      {.source, .target} := by decide
  have hconstantInner :
      (∑ _side : TangentEndpointSide, disjointCharge / 4) =
        disjointCharge / 2 := by
    rw [huniv]
    simp
    ring
  have hconstantOuter :
      (∑ _side : TangentEndpointSide, disjointCharge / 2) =
        disjointCharge := by
    rw [huniv]
    simp
    ring
  have hinner : ∀ leftSide : TangentEndpointSide,
      (∑ rightSide : TangentEndpointSide,
        (disjointCharge / 4 +
          if tangentEndpointLabel source target leftSide left =
              tangentEndpointLabel source target rightSide right
            then sharedCharge
              (tangentEndpointLabel source target leftSide left)
            else 0)) =
        disjointCharge / 2 +
          (if tangentRequestHasLabel source target
              (tangentEndpointLabel source target leftSide left) right
            then sharedCharge
              (tangentEndpointLabel source target leftSide left)
            else 0) := by
    intro leftSide
    rw [Finset.sum_add_distrib, hconstantInner]
    exact congrArg (fun value ↦ disjointCharge / 2 + value)
      (sum_endpointLabel_eq_sharedCharge source target right
        (tangentEndpointLabel source target leftSide left)
        (sharedCharge
          (tangentEndpointLabel source target leftSide left))
        (hendpointDistinct right))
  have houter :
      (∑ leftSide : TangentEndpointSide,
        (if tangentRequestHasLabel source target
            (tangentEndpointLabel source target leftSide left) right
          then sharedCharge
            (tangentEndpointLabel source target leftSide left)
          else 0)) =
        (if tangentRequestHasLabel source target (source left) right
          then sharedCharge (source left) else 0) +
        (if tangentRequestHasLabel source target (target left) right
          then sharedCharge (target left) else 0) := by
    rw [huniv]
    simp [tangentEndpointLabel]
  rw [hcast, Finset.sum_div]
  simp_rw [Finset.sum_div]
  calc
    (∑ leftSide : TangentEndpointSide,
        ∑ rightSide : TangentEndpointSide,
          (tangentEndpointEquationBudget N
              (tangentEndpointLabel source target leftSide left)
              (tangentEndpointLabel source target rightSide right) : ℝ) /
            denominator) ≤
      ∑ leftSide : TangentEndpointSide,
        ∑ rightSide : TangentEndpointSide,
          (disjointCharge / 4 +
            if tangentEndpointLabel source target leftSide left =
                tangentEndpointLabel source target rightSide right
              then sharedCharge
                (tangentEndpointLabel source target leftSide left)
              else 0) := by
        apply Finset.sum_le_sum
        intro leftSide _hleftSide
        apply Finset.sum_le_sum
        intro rightSide _hrightSide
        simpa only [denominator] using
          hEquation left right leftSide rightSide
    _ = ∑ leftSide : TangentEndpointSide,
        (disjointCharge / 2 +
          if tangentRequestHasLabel source target
              (tangentEndpointLabel source target leftSide left) right
            then sharedCharge
              (tangentEndpointLabel source target leftSide left)
            else 0) := by
        apply Finset.sum_congr rfl
        intro leftSide _hleftSide
        exact hinner leftSide
    _ = disjointCharge +
        ((if tangentRequestHasLabel source target (source left) right
          then sharedCharge (source left) else 0) +
        (if tangentRequestHasLabel source target (target left) right
          then sharedCharge (target left) else 0)) := by
        rw [Finset.sum_add_distrib, hconstantOuter, houter]
    _ = _ := by ring

/-! ## Effective-density bounds for one endpoint equation -/





/-! ## Paper-scale pair arithmetic -/





/-! ## The literal `1/8` coefficient arithmetic -/





end

end Erdos390.WholePaper

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal008_038.{u_1} := by
  exact @Erdos390.WholePaper.tangentOrderedPairEndpointBudget_div_le_charges_of_equationBounds
