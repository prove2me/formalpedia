-- Prove2me | solution 1 for EmergentGeometry.BitThreads.value_le_cutWeight
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:35:23.03225+00:00
-- url     : https://prove2.me/submissions/a0ccdbba-724f-4321-ab61-b8eda8546049

-- Sol generated from Novelty/EREPRBitThreads.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBitThreads
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRThroatCapacity
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Theorems.Thm_EmergentGeometry_cutWeight_eq_crossSum

/-!
# Bit threads: flows through an Einstein–Rosen bridge

The Ryu–Takayanagi prescription used in `Novelty.EmergentGeometryEntropyCone`
measures entanglement by *cutting* the bulk.  The dual "bit thread" picture
measures it by *flowing* through the bulk: entanglement is the maximal number of
Planck-thickness threads that can be routed from one boundary region to the
other.  This file introduces flows (`BitThreads`) on a bulk geometry and proves
the duality inequality

  `value(flow) ≤ area(any separating surface)`,

hence `value ≤ throat`, together with a matching flow for the elementary
one-throat wormhole, where the bound is attained: **max-flow = min-cut for a
single Einstein–Rosen bridge**.

Main results:

* `cutWeight_eq_crossSum` — the area of a surface as a one-sided double sum
  (the form flows interact with).
* `sum_antisymm_zero` — an antisymmetric flow contributes nothing inside a
  region; only the flux through its boundary survives.
* `BitThreads.value_le_cutWeight`, `BitThreads.value_le_throat` — **weak
  duality**: no thread configuration can carry more than the cross-section of the
  bridge.
* `pairThreads_value`, `pairModel_maxflow_eq_throat` — the bound is sharp: the
  elementary wormhole of weight `w` admits threads of value exactly `w`, equal to
  its throat capacity and to half its mutual information.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  If ER=EPR is more than a slogan, the entanglement of
a boundary pair should be *transportable* through the bridge: there should exist
a divergence-free, capacity-respecting flow whose flux equals the bridge
cross-section.

EXPERIMENT (Experimenter).  Weak duality is a two-step computation: (i) the flux
out of the source region equals the flux out of *any* admissible region
containing it (conservation kills the extra cells), and (ii) the internal part of
that flux cancels by antisymmetry, leaving a boundary term bounded by the
capacities.  Both steps are `Finset` identities: `Finset.sum_subset` and the
antisymmetric-sum-vanishing lemma.

ANALYSIS (Analyst).  The proof never uses finiteness beyond summability, and
never uses symmetry of the weights except through `cutWeight_eq_crossSum`.  The
converse (strong duality, i.e. existence of a saturating flow in general) is a
max-flow–min-cut theorem and is left as an explicit open direction; we verify it
by hand in the one-throat case.

CRITIQUE (Critic).  `capacity` is stated one-sidedly (`flow x y ≤ weight x y`);
combined with `antisymm` and symmetry of `weight` this is equivalent to
`|flow x y| ≤ weight x y`, so nothing is lost, and the sharp example shows the
class of flows is not degenerate.
-/

noncomputable section

open EmergentGeometry

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Areas as one-sided sums -/

omit [Fintype V] [DecidableEq V] in
/-- An antisymmetric kernel summed over a square index set vanishes. -/
theorem sum_antisymm_zero (φ : V → V → ℝ) (hanti : ∀ x y, φ x y = -φ y x) (S : Finset V) :
    ∑ x ∈ S, ∑ y ∈ S, φ x y = 0 := by
  have key : ∑ x ∈ S, ∑ y ∈ S, φ x y = ∑ x ∈ S, ∑ y ∈ S, (-(φ x y)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hanti y x
  simp only [Finset.sum_neg_distrib] at key
  linarith


omit [DecidableEq V] in
/-- The same area as a sum over the two sides of the surface. -/
theorem cutWeight_eq_sum_sides (G : BulkGraph V) (f : Region V) :
    cutWeight G f = ∑ x ∈ univ.filter (fun x => f x = true),
      ∑ y ∈ univ.filter (fun y => f y = false), G.weight x y := by
  rw [cutWeight_eq_crossSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : f x = true
  · rw [if_pos hx, Finset.sum_filter]
    exact Finset.sum_congr rfl fun y _ => by
      by_cases hy : f y = false <;> simp [hx, hy]
  · rw [if_neg hx]
    exact Finset.sum_eq_zero fun y _ => by simp [hx]

/-! ## Bit threads -/


variable {G : BulkGraph V}






/-! ## Sharpness: threading the elementary wormhole -/






open EmergentGeometry in
theorem solution(T : BitThreads G) {A B σ : Region V}
    (hcons : T.Conserved A B) (hsep : Separates A B σ) :
    T.value A ≤ cutWeight G σ := by
  set S : Finset V := univ.filter (fun x => σ x = true) with hS
  set SA : Finset V := univ.filter (fun x => A x = true) with hSA
  -- (1) the flux out of the sources equals the flux out of the whole region `σ`
  have hsub : SA ⊆ S := by
    intro x hx
    rw [hSA, mem_filter] at hx
    rw [hS, mem_filter]
    exact ⟨mem_univ x, hsep.1 x hx.2⟩
  have hstep1 : T.value A = ∑ x ∈ S, T.div x := by
    refine Finset.sum_subset hsub fun x hxS hxA => ?_
    have hσx : σ x = true := by simpa [hS] using hxS
    have hA : A x = false := by simpa [hSA] using hxA
    have hB : B x = false := by
      by_contra hB'
      have hBx : B x = true := by
        cases h' : B x
        · exact absurd h' hB'
        · rfl
      rw [hsep.2 x hBx] at hσx
      exact Bool.noConfusion hσx
    exact hcons x hA hB
  -- (2) the flux inside `σ` cancels; only the flux through its surface survives
  have hsplit : ∀ x : V, T.div x = ∑ y ∈ S, T.flow x y + ∑ y ∈ Sᶜ, T.flow x y := by
    intro x
    rw [BitThreads.div, ← Finset.sum_add_sum_compl S (T.flow x)]
  have hstep2 : ∑ x ∈ S, T.div x = ∑ x ∈ S, ∑ y ∈ Sᶜ, T.flow x y := by
    rw [Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_add_distrib,
      sum_antisymm_zero T.flow T.antisymm S, zero_add]
  -- (3) capacities bound the surviving flux by the area
  have hcompl : Sᶜ = univ.filter (fun y => σ y = false) := by
    ext y
    simp [hS, Bool.not_eq_true]
  have hstep3 : ∑ x ∈ S, ∑ y ∈ Sᶜ, T.flow x y ≤ cutWeight G σ := by
    rw [cutWeight_eq_sum_sides, ← hS, hcompl]
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => T.capacity x y
  rw [hstep1, hstep2]
  exact hstep3
