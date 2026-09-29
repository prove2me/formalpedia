-- Prove2me | solution 1 for displacement_convex
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:29:42.299112+00:00
-- url     : https://prove2.me/submissions/aaa47ffe-9f1a-4034-a165-825f124a39e4

-- Sol generated from Algebra/OISCC/OrbitIteration.lean
import Mathlib
import Definitions.Def_Algebra_OISCC_OrbitIteration

/-! # CatalogBuild.Speculative.OISCC.OrbitIteration

Auto-generated from theorem catalog database.
Domain: Speculative/OISCC
Declarations: 16
-/

noncomputable section


















theorem solution: ConvexOn ℝ (Set.Ioi 0) (fun x => d_oi x - x) := by
  apply_rules [ convexOn_of_deriv2_nonneg, convex_Ioi ];
  · exact ContinuousOn.sub ( ContinuousOn.sub ( Real.continuousOn_exp ) ( Real.continuousOn_log.mono fun x hx => ne_of_gt hx ) ) continuousOn_id;
  · exact DifferentiableOn.sub ( DifferentiableOn.sub ( Real.differentiable_exp.differentiableOn ) ( Real.differentiableOn_log.mono fun x hx => ne_of_gt <| interior_subset hx ) ) differentiableOn_id;
  · unfold d_oi;
    refine' DifferentiableOn.congr _ _;
    exacts [ fun x => Real.exp x - 1 / x - 1, DifferentiableOn.sub ( DifferentiableOn.sub ( Real.differentiable_exp.differentiableOn ) ( DifferentiableOn.div ( differentiableOn_const _ ) differentiableOn_id fun x hx => ne_of_gt <| interior_subset hx ) ) ( differentiableOn_const _ ), fun x hx => by norm_num [ Real.differentiableAt_exp, Real.differentiableAt_log, ne_of_gt <| interior_subset hx ] ];
  · -- Let's calculate the first derivative of $d(x) - x$.
    have h_deriv : ∀ x > 0, deriv (fun x => d_oi x - x) x = Real.exp x - 1 / x - 1 := by
      intro x hx; unfold d_oi; norm_num [ Real.differentiableAt_exp, Real.differentiableAt_log, hx.ne' ] ;
    -- Let's calculate the second derivative of $d(x) - x$.
    have h_deriv2 : ∀ x > 0, deriv^[2] (fun x => d_oi x - x) x = Real.exp x + 1 / x^2 := by
      have h_deriv2 : ∀ x > 0, deriv^[2] (fun x => d_oi x - x) x = deriv (fun x => Real.exp x - 1 / x - 1) x := by
        exact fun x hx => Filter.EventuallyEq.deriv_eq ( Filter.eventuallyEq_of_mem ( Ioi_mem_nhds hx ) fun y hy => h_deriv y hy );
      intro x hx; rw [ h_deriv2 x hx ] ; norm_num [ Real.differentiableAt_exp, differentiableAt_inv, hx.ne' ] ;
    exact fun x hx => h_deriv2 x ( interior_subset hx ) ▸ add_nonneg ( Real.exp_nonneg x ) ( one_div_nonneg.mpr ( sq_nonneg x ) )
