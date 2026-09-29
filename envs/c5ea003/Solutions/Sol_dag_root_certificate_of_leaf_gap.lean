-- Prove2me | solution 1 for dag_root_certificate_of_leaf_gap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:50:36.097618+00:00
-- url     : https://prove2.me/submissions/b8d63792-9f9b-4611-8db1-1a2a07e322d5

-- Sol generated from MachineLearning/TropicalDAGRobustness.lean
import Mathlib

/-!
# Tropical Certified Robustness for DAG-Aggregated Decision Rules

This file formalizes a compositional robustness framework for multiclass classifiers
whose decision procedures are represented by finite rooted DAGs built from monotone
1-Lipschitz tropical primitives (`max`, `min`, score-difference comparisons).

## Mathematical Overview

Given a score map `score : (ι → ℝ) → C → ℝ` that is `K`-Lipschitz in the L∞ norm,
and a decision procedure built from pairwise score comparisons aggregated through
a DAG of monotone tropical operations, we prove that the decision is invariant
under perturbations of size `ε` whenever pathwise bottleneck margins exceed `2·K·ε`.

The key mathematical insight is that **pathwise bottleneck margins in an arbitrary
acyclic tropical decision graph compose correctly with pairwise logit-gap perturbation
bounds**. This unifies:
1. One-vs-all argmax certificates (star DAG with min aggregation)
2. Sequential elimination / tournament certificates (chain DAG)

## Main Results

### Foundational Lemmas
* `abs_sub_pairwise_gap_le` — Triangle inequality for pairwise score gaps
* `pairwise_gap_perturbation_le_two_mul` — Score gap perturbation bounded by `2·K·ε`
* `abs_max_sub_max_le_max_abs_sub` — Max is 1-Lipschitz (nonexpansive)
* `abs_min_sub_min_le_max_abs_sub` — Min is 1-Lipschitz (nonexpansive)

### Finset Stability
* `Finset.inf'_abs_sub_le` — `Finset.inf'` is nonexpansive
* `Finset.sup'_abs_sub_le` — `Finset.sup'` is nonexpansive
* `positive_inf'_of_pointwise_lower_bound` — Positivity from pointwise bounds

### DAG Certificate
* `dag_root_certificate_of_leaf_gap` — Root certificate positivity under perturbation

### Corollaries
* `one_vs_all_robust_of_margin` — Classical argmax robustness from runner-up margin
* `sequential_elimination_robust` — Sequential elimination robustness from stagewise margins
* `decision_invariant_of_dag_certificate` — Full end-to-end decision invariance
-/

open Finset

noncomputable section

/-! ## Section 1: Foundational Real-Analysis Lemmas -/





/-! ## Section 2: Finset Inf'/Sup' Stability -/




/-! ## Section 3: DAG Root Certificate Theorem -/

/-
**Main DAG certificate theorem.**

Given a finite DAG with a recursive certificate function where:
- leaf certificates perturb by at most `Δ`,
- internal nodes aggregate children via monotone 1-Lipschitz operations
  (perturbation at a node ≤ sup of perturbations at its children),
- the root certificate at the clean input exceeds `Δ`,

then the root certificate remains strictly positive under perturbation.

The proof proceeds by strong induction on `rank`, showing that the certificate
perturbation at every node is bounded by `Δ`. Since the root certificate
exceeds `Δ`, it remains positive.
-/

/-
Auxiliary lemma: under the DAG hypotheses, the perturbation at every node
is bounded by `Δ`. This is the inductive core of the DAG certificate theorem.
-/

/-! ## Section 4: One-vs-All Argmax Robustness Corollary -/


/-! ## Section 5: Sequential Elimination Robustness Corollary -/


/-! ## Section 6: Full End-to-End Decision Invariance -/

/-
**End-to-end decision invariance theorem.**

Combines score-map Lipschitz continuity, DAG certificate stability, and
decision determinism to conclude that the final classification is invariant
on the entire L∞ ball of radius `ε`.

The proof has three steps:
1. Score perturbation: `∀ c, |score z c - score x c| ≤ K * ε`
2. Certificate stability: by induction on rank, every DAG node's certificate
   changes by at most `2·K·ε` (leaves use pairwise gap bound, internal nodes
   use monotone 1-Lipschitz aggregation)
3. Decision invariance: since `dagCert (score x) root > 2·K·ε > 0` and
   `dagCert (score z) root > 0`, the decision is the same by `hdecide`.

This theorem subsumes both the one-vs-all argmax certificate and the
sequential elimination certificate as special cases.
-/


theorem solution    {V : Type*} [Fintype V] [DecidableEq V]
    (root : V)
    (children : V → Finset V)
    (rank : V → ℕ)
    (cert_x cert_z : V → ℝ)
    (Δ : ℝ)
    (_ : 0 ≤ Δ)
    (hacyclic : ∀ {u v}, v ∈ children u → rank v < rank u)
    (hleaf :
      ∀ u, children u = ∅ →
        |cert_x u - cert_z u| ≤ Δ)
    (hmono_lip :
      ∀ u, ∀ hne : (children u).Nonempty,
        |cert_x u - cert_z u| ≤
          (children u).sup' hne fun v => |cert_x v - cert_z v|)
    (hroot_pos :
      Δ < cert_x root) :
    0 < cert_z root := by
      -- We prove that the perturbation bound holds for every node in the DAG.
      have h_node_perturbation_bound : ∀ u, |cert_x u - cert_z u| ≤ Δ := by
        -- We prove the perturbation bound using induction on the rank of the node in the DAG.
        have h_ind : ∀ k, ∀ u, rank u = k → |cert_x u - cert_z u| ≤ Δ := by
          intro k;
          induction' k using Nat.strong_induction_on with k ih;
          intro u hu;
          by_cases h : ( children u ).Nonempty <;> simp_all +decide;
          obtain ⟨ v, hv₁, hv₂ ⟩ := hmono_lip u h; exact le_trans hv₂ ( ih _ ( by linarith [ hacyclic hv₁ ] ) _ rfl ) ;
        exact fun u => h_ind _ _ rfl;
      linarith [ abs_le.mp ( h_node_perturbation_bound root ) ]
