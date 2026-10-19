-- Prove2me | Definitions.Def_AT260939824_ContinuousPriorityCuts
-- name    : AT260939824_ContinuousPriorityCuts
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:42:42.129037+00:00
-- url     : https://prove2.me/theorems/aeb760f8-6f88-4896-bc1b-75d217080d27
-- title:
--   Continuity of finite priority-cut iterations
-- statement:
--   Let $Y$ be a parameter space and $I$ an arbitrary index type. Assume each index has a finite neighborhood, with continuously varying discrete neighborhood lists, priorities, and integer centers. For $P\ge1$ and cut scale $L\ge32P$, every finite stage of priority-cut selection gives a continuous integer cut pair at each index.
--
--   The locality interface requires equality only on the relevant finite neighborhood; no finiteness assumption on all of $I$ is imposed.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 3; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/ContinuousPriorityCuts.lean, selected declaration lines 21-25, 27-46, 48-97; SHA-256 5dca47c9479e314549434e1660b7d88df4aa0a1130e8cbdea0d4107b09181a08. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_PriorityCuts
import Init
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Interval
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Int

set_option autoImplicit false

/-!
# Continuity of finite priority-cut processing

The marker index type may be infinite. For each fixed index, the finite
neighbor list, priority, and integer center vary continuously with the
parameter. The neighbor-list space is given a discrete topology. Every
finite stage of the actual `priorityCutIteration` is then continuous.
This is a local continuity result; constructing an orbit-coordinate
parameterization of marker indices and the final CW atlas is separate.
-/

namespace AbelianTargets

noncomputable section
open Filter Topology

 theorem locally_equal_of_continuous {Y A : Type*}
    [TopologicalSpace Y] [TopologicalSpace A] [DiscreteTopology A]
    {f : Y → A} (hf : Continuous f) (y : Y) :
    ∀ᶠ z in 𝓝 y, f z = f y := by
  exact hf.continuousAt.eventually ((isOpen_discrete ({f y} : Set A)).mem_nhds rfl)

theorem earlierPriorityCuts_congr {I : Type*} {P : ℕ}
    (N N' : PriorityNeighborhood I P) (old old' : I → ℤ × ℤ)
    (n : ℕ) (x : I) (hnear : N.nearby x = N'.nearby x)
    (hpriority : ∀ i ∈ N'.nearby x, N.priority i = N'.priority i)
    (hold : ∀ i ∈ N'.nearby x, old i = old' i) :
    earlierPriorityCuts N old n x = earlierPriorityCuts N' old' n x := by
  classical
  unfold earlierPriorityCuts
  have hfilter : (N.nearby x).filter (fun i => (N.priority i).val < n) =
      (N'.nearby x).filter (fun i => (N'.priority i).val < n) := by
    rw [hnear]
    apply Finset.filter_congr
    intro i hi
    rw [hpriority i hi]
  apply Finset.biUnion_congr hfilter
  intro i hi
  have hi' : i ∈ N'.nearby x := by
    rw [hnear] at hi
    exact (Finset.mem_filter.mp hi).1
  rw [hold i hi']

/-- A finite number of priority stages needs only finitely many local
inputs at each parameter. No finiteness assumption on `I` is needed. -/
theorem continuous_priorityCutIteration {Y I : Type*}
    [TopologicalSpace Y] [TopologicalSpace (Finset I)]
    [DiscreteTopology (Finset I)] {P L : ℕ}
    (N : Y → PriorityNeighborhood I P)
    (hP : 1 ≤ P) (hL : 32 * P ≤ L) (center : Y → I → ℤ)
    (hnear : ∀ i, Continuous (fun y => (N y).nearby i))
    (hpriority : ∀ i, Continuous (fun y => (N y).priority i))
    (hcenter : ∀ i, Continuous (fun y => center y i)) :
    ∀ n i, Continuous (fun y => priorityCutIteration (N y) hP hL (center y) n i) := by
  classical
  intro n
  induction n with
  | zero =>
      intro i
      simpa only [priorityCutIteration] using
        (continuous_of_discreteTopology (f := fun z : ℤ =>
          (z-3*L,z+2*L))).comp (hcenter i)
  | succ n ih =>
      intro i
      apply continuous_iff_continuousAt.mpr
      intro y
      have hn := locally_equal_of_continuous (hnear i) y
      have hp := locally_equal_of_continuous (hpriority i) y
      have hc := locally_equal_of_continuous (hcenter i) y
      have ho := locally_equal_of_continuous (ih i) y
      have hs : ∀ᶠ z in 𝓝 y, ∀ j ∈ (N y).nearby i,
          (N z).priority j = (N y).priority j ∧
            priorityCutIteration (N z) hP hL (center z) n j =
              priorityCutIteration (N y) hP hL (center y) n j := by
        apply ((N y).nearby i).eventually_all.mpr
        intro j hj
        exact (locally_equal_of_continuous (hpriority j) y).and
          (locally_equal_of_continuous (ih j) y)
      have he : ∀ᶠ z in 𝓝 y,
          priorityCutIteration (N z) hP hL (center z) (n+1) i =
            priorityCutIteration (N y) hP hL (center y) (n+1) i := by
        filter_upwards [hn, hp, hc, ho, hs] with z hn hp hc ho hs
        have hearlier := earlierPriorityCuts_congr (N z) (N y)
          (priorityCutIteration (N z) hP hL (center z) n)
          (priorityCutIteration (N y) hP hL (center y) n) n i hn
          (fun j hj => (hs j hj).1) (fun j hj => (hs j hj).2)
        simp only [priorityCutIteration, hp, hc]
        split_ifs
        · simp only [hearlier]
        · exact ho
      have he' : (fun z => priorityCutIteration (N z) hP hL (center z) (n+1) i)
          =ᶠ[𝓝 y] (fun _ => priorityCutIteration (N y) hP hL (center y) (n+1) i) := he
      exact continuousAt_const.congr he'.symm



end
end AbelianTargets


