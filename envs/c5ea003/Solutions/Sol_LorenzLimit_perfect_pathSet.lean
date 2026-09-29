-- Prove2me | solution 1 for LorenzLimit.perfect_pathSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:36:27.694911+00:00
-- url     : https://prove2.me/submissions/d1a19cc1-15f6-44f7-829e-57bfc2455f82

-- Sol generated from Novelty/StrangeAttractorTopology.lean
import Mathlib
import Definitions.Def_Novelty_StrangeAttractorInverseLimit
import Definitions.Def_Novelty_StrangeAttractorTopology

/-!
# Strange attractors as algebraic objects, IV: the topology of the inverse limit

The inverse limit of the finite path diagram of a finite directed graph is not merely a set:
it carries the inverse-limit topology, inherited from the product of discrete finite sets.
Here we prove that it has exactly the topological features expected of a strange attractor's
transversal structure:

* `isClosed_pathSet`, `isCompact_pathSet` : the orbit space is a compact (closed) subset of
  the Cantor-type product space, so the inverse limit of finite graphs is compact;
* `continuous_shift` : the shift is continuous, so `(PathSpace E, shift)` is a topological
  dynamical system;
* `cantorMap_isClosedEmbedding` : if every vertex branches (out-degree `≥ 2`) the attractor
  contains a topologically embedded Cantor set;
* `uncountable_pathSpace` : consequently the attractor is uncountable, while every finite
  approximant is finite — the inverse limit is a genuinely infinite object;
* `perfect_pathSet` : a branching attractor has no isolated orbits, so it is a perfect,
  compact, totally disconnected, Hausdorff space.

Together with the compactness, total disconnectedness and Hausdorffness instances this says
that a branching symbolic attractor is a Cantor-type space.
-/

open LorenzLimit

variable {V : Type*} [Fintype V] [TopologicalSpace V] [DiscreteTopology V] {E : V → V → Bool}

/-! ## Compactness and total disconnectedness -/







/-! ## The shift is continuous -/


/-! ## An embedded Cantor set -/


variable (h : Branching E)



omit [Fintype V] [TopologicalSpace V] [DiscreteTopology V] in
theorem succ_ne (v : V) : succ₀ h v ≠ succ₁ h v := (h v).choose_spec.choose_spec.1











/-! ## No isolated orbits: the attractor is perfect -/


omit [Fintype V] [TopologicalSpace V] [DiscreteTopology V] in
theorem altSucc_ne (v w : V) : altSucc h v w ≠ w := by
  unfold altSucc
  by_cases hc : succ₀ h v = w
  · rw [if_pos hc]
    intro hcon
    exact succ_ne h v (hc.trans hcon.symm)
  · rw [if_neg hc]
    exact hc



omit [Fintype V] [TopologicalSpace V] [DiscreteTopology V] in
theorem altPath_agree (x : PathSpace E) (n : ℕ) {k : ℕ} (hk : k ≤ n) :
    (altPath h x n).1 k = x.1 k := by
  show (if k ≤ n then _ else _) = _
  rw [if_pos hk]

omit [Fintype V] [TopologicalSpace V] [DiscreteTopology V] in
theorem altPath_ne (x : PathSpace E) (n : ℕ) : (altPath h x n).1 (n + 1) ≠ x.1 (n + 1) := by
  show (if n + 1 ≤ n then _ else _) ≠ _
  rw [if_neg (by omega)]
  simpa [deadEndFreeSeq] using altSucc_ne h (x.1 n) (x.1 (n + 1))




open LorenzLimit.Branching in
omit [Fintype V] in
include h in
theorem solution: Perfect (pathSet E) := by
  refine ⟨isClosed_pathSet, ?_⟩
  intro x hx
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨W, hWU, hWopen, hxW⟩ := mem_nhds_iff.1 hU
  obtain ⟨I, u, hu, hIW⟩ := isOpen_pi_iff.1 hWopen x hxW
  set n := I.sup id with hn
  refine ⟨(altPath h ⟨x, hx⟩ n).1, ⟨hWU ?_, (altPath h ⟨x, hx⟩ n).2⟩, ?_⟩
  · apply hIW
    intro i hi
    have hile : i ≤ n := Finset.le_sup (f := id) hi
    rw [altPath_agree h ⟨x, hx⟩ n hile]
    exact (hu i hi).2
  · intro hcon
    exact altPath_ne h ⟨x, hx⟩ n (congrFun hcon (n + 1))
