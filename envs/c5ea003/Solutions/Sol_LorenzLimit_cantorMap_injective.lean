-- Prove2me | solution 1 for LorenzLimit.cantorMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:36:26.395251+00:00
-- url     : https://prove2.me/submissions/029c0435-2620-4537-95b0-6230a36d5ef7

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










open LorenzLimit in
omit [Fintype V] [TopologicalSpace V] [DiscreteTopology V] in
theorem solution(v₀ : V) : Function.Injective (cantorMap h v₀) := by
  intro b c hbc
  have hseq : ∀ n, cantorSeq h v₀ b n = cantorSeq h v₀ c n := fun n =>
    congrFun (congrArg Subtype.val hbc) n
  funext n
  have hn := hseq (n + 1)
  have hn0 := hseq n
  by_cases hb : b n <;> by_cases hc : c n
  · simp [hb, hc]
  · exfalso
    rw [show cantorSeq h v₀ b (n + 1) = succ₁ h (cantorSeq h v₀ b n) by
      simp [cantorSeq, hb],
      show cantorSeq h v₀ c (n + 1) = succ₀ h (cantorSeq h v₀ c n) by
      simp [cantorSeq, hc], ← hn0] at hn
    exact succ_ne h _ hn.symm
  · exfalso
    rw [show cantorSeq h v₀ b (n + 1) = succ₀ h (cantorSeq h v₀ b n) by
      simp [cantorSeq, hb],
      show cantorSeq h v₀ c (n + 1) = succ₁ h (cantorSeq h v₀ c n) by
      simp [cantorSeq, hc], ← hn0] at hn
    exact succ_ne h _ hn
  · simp at hb hc
    simp [hb, hc]
