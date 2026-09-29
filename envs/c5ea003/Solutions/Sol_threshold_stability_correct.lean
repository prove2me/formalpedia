-- Prove2me | solution 1 for threshold_stability_correct
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T10:21:05.418983+00:00
-- url     : https://prove2.me/submissions/687c71bc-3a3e-41fe-ab57-37dcec0552c4

-- Sol generated from Tropical/GraphTheory/PoincareThreshold.lean
import Mathlib
import Definitions.Def_Tropical_GraphTheory_PoincareThreshold
/-
  Poincaré Threshold for Metric Filtrations

  This file establishes rigorous foundations for the Poincaré threshold—the
  critical scale parameter at which a metric-indexed filtration first exhibits
  a target topological property. We formalize:

  1. The Rips graph construction and its monotonicity
  2. Approximate isometries and the interleaving theorem
  3. Abstract metric filtrations and threshold stability
  4. Covering-number bounds on the Poincaré threshold
  5. A Lipschitz stability result for thresholds under perturbation
-/

open scoped NNReal

noncomputable section

/-! ## Part 1: Rips Graph Construction -/



/-! ## Part 2: Approximate Isometries -/



/-! ## Part 3: Abstract Metric Filtrations -/




/-- **Threshold Antitone Principle**: If filtration F dominates G (F's property
    implies G's), then G's threshold ≤ F's threshold, because G's level set
    is a superset of F's. -/
theorem threshold_antitone {F G : MetricFiltration}
    (hdom : MetricFiltration.Dominates F G)
    (hFne : {ε : ℝ | F.property ε}.Nonempty)
    (hGbdd : BddBelow {ε : ℝ | G.property ε}) :
    G.threshold ≤ F.threshold := by
  apply_rules [csInf_le_csInf]

/-! ## Part 4: Shifted Filtrations and Stability -/


/-
The threshold of a shifted filtration equals the original threshold plus δ.
-/
theorem threshold_shift (F : MetricFiltration) (δ : ℝ)
    (hne : {ε : ℝ | F.property ε}.Nonempty)
    (hbdd : BddBelow {ε : ℝ | F.property ε}) :
    (F.shift δ).threshold = F.threshold + δ := by
  unfold MetricFiltration.threshold MetricFiltration.shift;
  rw [ @csInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
  · exact ⟨ hne.choose + δ, by simpa using hne.choose_spec ⟩;
  · exact fun x hx => by linarith [ show sInf { ε : ℝ | F.property ε } ≤ x - δ from csInf_le hbdd hx ] ;
  · intro w hw; rcases exists_lt_of_csInf_lt ( hne ) ( show InfSet.sInf { ε | F.property ε } < w - δ by linarith ) with ⟨ x, hx, hx' ⟩ ; exact ⟨ x + δ, by aesop, by linarith ⟩ ;

/-
**Stability Theorem (correct interleaving direction)**: If each filtration's
    shift dominates the other—meaning F.property(ε-δ) → G.property(ε) and
    G.property(ε-δ) → F.property(ε)—then the thresholds differ by at most δ.

    This corresponds to the standard δ-interleaving in persistent homology:
    the shifted version of F is "easier" than G, and vice versa.
-/

/-! ## Part 5: Rips Connectivity Filtration -/


/-! ## Part 6: Covering Numbers and Threshold Bounds -/



/-! ## Part 7: Edge Count Monotonicity -/



/-! ## Part 8: Approximate Isometry Composition -/


/-! ## Part 9: Threshold Shift Bound -/

/-
One-sided stability: if F.property ε ⟹ G.property (ε+δ),
    then G.threshold ≤ F.threshold + δ.
-/


theorem solution{F G : MetricFiltration} {δ : ℝ} (_hδ : 0 ≤ δ)
    (hFG : MetricFiltration.Dominates (F.shift δ) G)
    (hGF : MetricFiltration.Dominates (G.shift δ) F)
    (hFne : {ε : ℝ | F.property ε}.Nonempty)
    (hGne : {ε : ℝ | G.property ε}.Nonempty)
    (hFbdd : BddBelow {ε : ℝ | F.property ε})
    (hGbdd : BddBelow {ε : ℝ | G.property ε}) :
    |F.threshold - G.threshold| ≤ δ := by
  refine' abs_sub_le_iff.mpr ⟨ _, _ ⟩;
  · rw [ sub_le_iff_le_add' ];
    convert threshold_antitone _ _ _ using 1;
    rotate_left;
    exact ⟨ fun ε => G.property ( ε - δ ), fun ε₁ ε₂ h => G.mono _ _ ( by linarith ) ⟩;
    · exact hGF;
    · exact ⟨ hGne.choose + δ, by simpa using hGne.choose_spec ⟩;
    · assumption;
    · convert threshold_shift _ _ _ _ |> Eq.symm using 1; all_goals assumption;
  · have := @threshold_antitone ( F.shift δ ) G ?_ ?_ ?_;
    · linarith [ threshold_shift F δ hFne hFbdd ];
    · assumption;
    · obtain ⟨ ε, hε ⟩ := hFne;
      exact ⟨ ε + δ, by simpa [ MetricFiltration.shift ] using hε ⟩;
    · assumption
