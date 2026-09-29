-- Prove2me | Definitions.Def_Novelty_StrangeAttractorTopology
-- name    : Novelty_StrangeAttractorTopology
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:42:43.50299+00:00
-- url     : https://prove2.me/theorems/488ec2a8-0226-4362-bfec-d820016f2f45
-- title:
--   Aether Catalog definitions — Novelty_StrangeAttractorTopology
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.StrangeAttractorTopology`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/StrangeAttractorTopology.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_StrangeAttractorInverseLimit

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

namespace LorenzLimit

variable {V : Type*} [Fintype V] [TopologicalSpace V] [DiscreteTopology V] {E : V → V → Bool}

/-! ## Compactness and total disconnectedness -/

omit [Fintype V] in
theorem isClosed_pathSet : IsClosed (pathSet E) := by
  have : pathSet E = ⋂ n : ℕ, {x : ℕ → V | E (x n) (x (n + 1)) = true} := by
    ext x; simp [pathSet]
  rw [this]
  refine isClosed_iInter fun n => ?_
  have hcont : Continuous (fun x : ℕ → V => (x n, x (n + 1))) :=
    (continuous_apply n).prodMk (continuous_apply (n + 1))
  have : {x : ℕ → V | E (x n) (x (n + 1)) = true}
      = (fun x : ℕ → V => (x n, x (n + 1))) ⁻¹' {p : V × V | E p.1 p.2 = true} := rfl
  rw [this]
  exact (isClosed_discrete _).preimage hcont

theorem isCompact_pathSet : IsCompact (pathSet E) :=
  isClosed_pathSet.isCompact

instance instTopologicalSpacePathSpace : TopologicalSpace (PathSpace E) :=
  inferInstanceAs (TopologicalSpace (pathSet E))

instance instCompactSpacePathSpace : CompactSpace (PathSpace E) :=
  isCompact_iff_compactSpace.1 isCompact_pathSet

instance instT2SpacePathSpace : T2Space (PathSpace E) :=
  inferInstanceAs (T2Space (pathSet E))

instance instTotallyDisconnectedPathSpace : TotallyDisconnectedSpace (PathSpace E) :=
  inferInstanceAs (TotallyDisconnectedSpace (pathSet E))

/-! ## The shift is continuous -/


/-! ## An embedded Cantor set -/

section Branching

variable (h : Branching E)

/-- The first of two chosen successors of a vertex. -/
noncomputable def succ₀ (v : V) : V := (h v).choose

/-- The second of two chosen successors of a vertex. -/
noncomputable def succ₁ (v : V) : V := (h v).choose_spec.choose


omit [Fintype V] [TopologicalSpace V] [DiscreteTopology V] in
theorem edge_succ₀ (v : V) : E v (succ₀ h v) = true := (h v).choose_spec.choose_spec.2.1

omit [Fintype V] [TopologicalSpace V] [DiscreteTopology V] in
theorem edge_succ₁ (v : V) : E v (succ₁ h v) = true := (h v).choose_spec.choose_spec.2.2

/-- The binary tree of orbits determined by the branching structure. -/
noncomputable def cantorSeq (v₀ : V) (b : ℕ → Bool) : ℕ → V
  | 0 => v₀
  | k + 1 => if b k then succ₁ h (cantorSeq v₀ b k) else succ₀ h (cantorSeq v₀ b k)

/-- Every binary sequence names an orbit of the attractor. -/
noncomputable def cantorMap (v₀ : V) (b : ℕ → Bool) : PathSpace E :=
  ⟨cantorSeq h v₀ b, by
    intro n
    by_cases hb : b n
    · show E _ (if b n then _ else _) = true
      rw [if_pos hb]
      exact edge_succ₁ h _
    · show E _ (if b n then _ else _) = true
      rw [if_neg hb]
      exact edge_succ₀ h _⟩







/-! ## No isolated orbits: the attractor is perfect -/

include h in
open Classical in
/-- A successor of `v` different from a prescribed vertex `w`. -/
noncomputable def altSucc (v w : V) : V :=
  if succ₀ h v = w then succ₁ h v else succ₀ h v


omit [Fintype V] [TopologicalSpace V] [DiscreteTopology V] in
theorem edge_altSucc (v w : V) : E v (altSucc h v w) = true := by
  unfold altSucc
  by_cases hc : succ₀ h v = w
  · rw [if_pos hc]; exact edge_succ₁ h v
  · rw [if_neg hc]; exact edge_succ₀ h v

include h in
/-- An orbit agreeing with `x` up to time `n` and branching away at time `n + 1`. -/
noncomputable def altPath (x : PathSpace E) (n : ℕ) : PathSpace E := by
  refine ⟨fun k => if k ≤ n then x.1 k else
    deadEndFreeSeq h.noDeadEnds (altSucc h (x.1 n) (x.1 (n + 1))) (k - (n + 1)), ?_⟩
  intro k
  dsimp only
  rcases lt_trichotomy k n with hk | hk | hk
  · rw [if_pos (by omega), if_pos (by omega)]
    exact x.2 k
  · subst hk
    rw [if_pos (le_refl k), if_neg (by omega)]
    simp only [Nat.sub_self, deadEndFreeSeq]
    exact edge_altSucc h (x.1 k) (x.1 (k + 1))
  · rw [if_neg (by omega), if_neg (by omega)]
    have hstep : k + 1 - (n + 1) = (k - (n + 1)) + 1 := by omega
    rw [hstep]
    exact (h.noDeadEnds _).choose_spec




end Branching

end LorenzLimit


