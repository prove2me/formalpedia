-- Prove2me | Definitions.Def_Bridges_HierarchicalRobustness
-- name    : Bridges_HierarchicalRobustness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:26:18.506081+00:00
-- url     : https://prove2.me/theorems/f32d0b4d-6971-44f2-876b-5a31ab2f83d8
-- title:
--   Aether Catalog definitions — Bridges_HierarchicalRobustness
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.HierarchicalRobustness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/HierarchicalRobustness.lean by skeleton subtraction
import Mathlib
/-
# Compositional Robustness for Hierarchical Decision Trees

This module formalizes compositional robustness theorems for hierarchical classifiers
built from binary decision trees. The key insight is that local margin certificates
along a root-to-leaf path compose into a global robustness guarantee.

## Main Results

- `hierarchical_robust_of_path_margins`: Local sign-preservation along a decision path
- `hierarchical_classifier_constant_on_ball`: Classifier invariance on a metric ball
- `robustness_of_radius_lt_path_certificate`: Explicit radius certificate via `Finset.inf'`
- `hierarchical_robust_of_summed_losses`: Additive perturbation budget variant

## Mathematical Context

In the GL3 tropical Satake robustness program, flat decoders (argmax, top-k, ECOC)
yield one-shot multiclass margin statements. Hierarchical trees introduce genuinely
new mathematics: robustness becomes a *pathwise composition* of local tropical margin
certificates. This module proves the fundamental composition principle.
-/

open Finset

variable {α ι γ : Type*} [MetricSpace α]

/-! ## Local Margin Definition -/

/-- The local chosen-vs-other margin at node `v`.
If the clean input goes right at `v`, the margin is `SR v x - SL v x`;
if it goes left, the margin is `SL v x - SR v x`.
A positive margin means the clean decision is strictly preferred. -/
def localMargin (goRight : ι → Bool) (SL SR : ι → α → ℝ) (v : ι) (x : α) : ℝ :=
  if goRight v then SR v x - SL v x else SL v x - SR v x

/-! ## Core Sign-Preservation Lemma -/


/-! ## Classifier Invariance -/


/-! ## Explicit Radius Certificate -/


/-! ## Additive Perturbation Budget Variant -/


/-! ## Helper: Margin Lipschitz from Aggregate Lipschitz -/


/-! ## Axiom verification -/


