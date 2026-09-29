-- Prove2me | solution 1 for Hadwiger.colorable_of_forall_finite_induce_colorable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:32:37.569767+00:00
-- url     : https://prove2.me/submissions/6c323f5e-a8f1-4a4c-adad-2d7a3d7a4035

-- Sol generated from Probability/HadwigerCompactness.lean
import Mathlib
import Definitions.Def_Probability_HadwigerInfinite
/-
  Compactness: from Finite Hadwiger to Infinite Hadwiger
  ======================================================

  This file proves the de Bruijn–Erdős colouring compactness theorem inside the
  development and uses it to show that Hadwiger's conjecture for finite graphs
  implies Hadwiger's conjecture for graphs of arbitrary cardinality.

  Main results:

  * `Hadwiger.colorable_of_forall_finite_induce_colorable` : **de Bruijn–Erdős**
    — if every finite induced subgraph of `G` is `n`-colourable then so is `G`.
  * `Hadwiger.exists_finite_not_colorable` : the contrapositive form.
  * `Hadwiger.hadwigerPropertyGen_of_hadwigerProperty` : `HadwigerProperty k`
    implies `HadwigerPropertyGen k` — the conjecture has no independent
    infinite content.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): Hadwiger's conjecture for infinite graphs should
    carry no information beyond the finite case, because both sides of the
    implication are "finitary": non-colourability is witnessed by a finite
    subgraph (compactness), and a minor of an induced subgraph is a minor.
  Experiment (Experimenter): the compactness half is a genuine topological
    argument — the colour space `V → Fin n` carries the product of discrete
    topologies, hence is compact by Tychonoff (`Pi.compactSpace`); for each
    ordered pair of vertices the "properly coloured" constraint is a closed
    subset (every subset of a discrete space is closed), and every finite
    subfamily of constraints is satisfiable by extending a colouring of the
    finite set of vertices involved.  `IsCompact.elim_finite_subfamily_closed`
    turns finite satisfiability into global satisfiability.
  Analysis (Analyst): the only non-formal points are the degenerate ones — the
    empty vertex type, and the need for `Nonempty (Fin n)` to extend a partial
    colouring, which is recovered from `n`-colourability of a single vertex.
  Critique (Critic): the statement is not vacuous: the hypothesis quantifies
    over `Finset V`, so for finite `V` it is implied by taking `S = univ`, and
    for infinite `V` it is strictly weaker than the conclusion a priori.
  Synthesis (PI): with `hadwiger_two` this yields the `k ≤ 2` cases for
    arbitrary graphs a second, independent way (see `hadwiger_gen_two'`), and
    it reduces every open case of the conjecture to its finite form.
  -- !-- Lab Notes -- !--
-/

open Hadwiger

open SimpleGraph Topology

variable {V : Type} {G : SimpleGraph V} {n k : ℕ}






open Hadwiger in
theorem solution    (h : ∀ S : Finset V, (G.induce (S : Set V)).Colorable n) : G.Colorable n := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨Coloring.mk (fun v => isEmptyElim v) (fun {x} => isEmptyElim x)⟩
  -- a single vertex shows there is at least one colour available
  obtain ⟨v₀⟩ := hV
  have hne : Nonempty (Fin n) :=
    ⟨(h {v₀}).some ⟨v₀, by simp⟩⟩
  letI : Inhabited (Fin n) := ⟨hne.some⟩
  letI : TopologicalSpace (Fin n) := ⊥
  haveI : DiscreteTopology (Fin n) := ⟨rfl⟩
  haveI : CompactSpace (V → Fin n) := Pi.compactSpace
  -- the constraint sets
  set C : V × V → Set (V → Fin n) :=
    fun p => {f | G.Adj p.1 p.2 → f p.1 ≠ f p.2} with hC
  have hclosed : ∀ p, IsClosed (C p) := by
    intro p
    have : C p = (fun f : V → Fin n => (f p.1, f p.2)) ⁻¹'
        {q : Fin n × Fin n | G.Adj p.1 p.2 → q.1 ≠ q.2} := rfl
    rw [this]
    exact (isClosed_discrete _).preimage
      ((continuous_apply p.1).prodMk (continuous_apply p.2))
  -- every finite subfamily is satisfiable
  have hfin : ∀ u : Finset (V × V), (⋂ p ∈ u, C p).Nonempty := by
    intro u
    set S : Finset V := u.image Prod.fst ∪ u.image Prod.snd with hS
    obtain ⟨c⟩ := h S
    refine ⟨fun x => if hx : x ∈ S then c ⟨x, by simpa using hx⟩ else default, ?_⟩
    simp only [Set.mem_iInter]
    intro p hp hadj
    have h1 : p.1 ∈ S := by
      simp only [hS, Finset.mem_union, Finset.mem_image]
      exact Or.inl ⟨p, hp, rfl⟩
    have h2 : p.2 ∈ S := by
      simp only [hS, Finset.mem_union, Finset.mem_image]
      exact Or.inr ⟨p, hp, rfl⟩
    simp only [dif_pos h1, dif_pos h2]
    exact c.valid (by exact hadj)
  -- compactness
  have hnonempty : (⋂ p, C p).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    obtain ⟨u, hu⟩ := isCompact_univ.elim_finite_subfamily_closed C hclosed
      (by rw [Set.univ_inter, hempty])
    rw [Set.univ_inter] at hu
    exact Set.not_nonempty_empty (hu ▸ hfin u)
  obtain ⟨f, hf⟩ := hnonempty
  rw [Set.mem_iInter] at hf
  exact ⟨Coloring.mk f (fun {x y} hxy => hf (x, y) hxy)⟩
