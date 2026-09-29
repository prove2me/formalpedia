-- Prove2me | solution 1 for PhantomTopology.lower_sup_upper_eq_standard
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:52:12.59518+00:00
-- url     : https://prove2.me/submissions/9ace151c-a9fb-400c-b96b-78978fcbbb4f

-- Sol generated from Logic/PosetTheory/PhantomTopologies.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_PhantomTopologies
/-
# Phantom Topologies

A phantom topology is an observer-indexed family of topologies.  This file makes
"agreement" precise as the supremum in Mathlib's (reverse-inclusion) lattice of
topologies and develops a chain of results from the general definition to two
substantive examples.

The literal proposed phantom number is degenerate: every topology has a
one-observer representation, obtained by letting that observer see the real
topology itself.  A nontrivial variant requires every observer to be strictly
finer than consensus.  For that variant, the standard topology on `ℝ` has a
genuine two-observer representation by the lower- and upper-limit topologies.
The proposed lower bound for nonmetrizable spaces is false: the indiscrete
space on `Bool` is nonmetrizable yet is the consensus of two strictly finer
Sierpiński topologies.
-/

open Set TopologicalSpace

open PhantomTopology

variable {X ι : Type*}










/-! ## The real line: two half-open observers -/















/-! ## A nonmetrizable two-observer counterexample -/










open PhantomTopology in
theorem solution:
    lowerTop ⊔ upperTop = (inferInstance : TopologicalSpace ℝ) := by
  apply TopologicalSpace.ext
  ext U
  constructor
  · rintro ⟨hlo, hup⟩
    rw [Metric.isOpen_iff]
    intro x hx
    obtain ⟨b, hb, hbsub⟩ := hlo x hx
    obtain ⟨a, ha, hasub⟩ := hup x hx
    refine ⟨min (x - a) (b - x), by simp only [lt_min_iff]; constructor <;> linarith, ?_⟩
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    have h₁ : |y - x| < x - a := lt_of_lt_of_le hy (min_le_left _ _)
    have h₂ : |y - x| < b - x := lt_of_lt_of_le hy (min_le_right _ _)
    rw [abs_lt] at h₁ h₂
    rcases le_or_gt x y with hxy | hxy
    · exact hbsub ⟨hxy, by linarith [h₂.2]⟩
    · exact hasub ⟨by linarith [h₁.1], le_of_lt hxy⟩
  · intro hU
    rw [Metric.isOpen_iff] at hU
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨ε, hε, hsub⟩ := hU x hx
      refine ⟨x + ε, by linarith, ?_⟩
      intro y hy
      apply hsub
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> [linarith [hy.1]; linarith [hy.2]]
    · intro x hx
      obtain ⟨ε, hε, hsub⟩ := hU x hx
      refine ⟨x - ε, by linarith, ?_⟩
      intro y hy
      apply hsub
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> [linarith [hy.1]; linarith [hy.2]]
