-- Prove2me | solution 1 for LorenzLimit.finPath_card_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:36:27.16414+00:00
-- url     : https://prove2.me/submissions/6c4a0e5a-e8a9-48df-a478-58f47ed7dfda

-- Sol generated from Novelty/StrangeAttractorInverseLimit.lean
import Mathlib
import Definitions.Def_Novelty_StrangeAttractorInverseLimit

/-!
# Strange attractors as algebraic objects, I: the inverse-limit theorem

This file deepens `Novelty.StrangeAttractorsAlgebraic`, where binary de Bruijn graphs were
used to build a Cantor-like inverse limit.  Here the construction is carried out for an
*arbitrary* finite directed graph, and the central conjecture of the research thread is
proved in full:

> the space of infinite orbits of a symbolic (graph) dynamical system **is** the inverse
> limit of the diagram of its finite path sets in the category of finite sets, the bonding
> maps being edge deletion.

A finite directed graph is encoded as a `Bool`-valued edge relation `E : V → V → Bool` on a
finite vertex type.  For each `n` the *finite* set `FinPath E n` of paths with `n` edges is
a `Fintype`, and `truncPath` deletes the last edge.  The main results are:

* `invLimitEquiv` : `PathSpace E ≃ InvLimit E`, the inverse-limit theorem;
* `invLimitEquiv_shift` / `shift_toInvLimit` : the shift is visible on the finite level;
* `truncPath_surjective` : with no dead ends the bonding maps are surjective, so the
  diagram is a genuine (non-degenerate) tower;
* `finPath_card_pos`: the finite approximants are nonempty when there are no dead ends;
* `ClosedWalk`, `PeriodicPoints`, `IsConjugate`: the vocabulary used downstream for the
  zeta function, the periodic-orbit count and conjugacy invariants.

The geometric Lorenz attractor is the inverse limit of its branched-manifold (template)
first-return graph; the theorems below are the algebraic skeleton of that statement, and
`Novelty.StrangeAttractorLorenzTemplate` instantiates them at the Lorenz template.
-/

open LorenzLimit

variable {V : Type*}

/-! ## Finite path sets and bonding maps -/









variable {E : V → V → Bool}


theorem PathSpace.edge (x : PathSpace E) (n : ℕ) : E (x.1 n) (x.1 (n + 1)) = true := x.2 n

/-! ## The inverse-limit theorem -/







/-! ## The shift -/






/-! ## Non-degeneracy of the tower -/





/-- With no dead ends every finite path set is nonempty, provided the graph has a vertex. -/
theorem finPath_nonempty (h : NoDeadEnds E) [Nonempty V] (n : ℕ) : Nonempty (FinPath E n) := by
  induction n with
  | zero =>
      obtain ⟨v⟩ := ‹Nonempty V›
      exact ⟨⟨fun _ => v, fun i => absurd i.isLt (by omega)⟩⟩
  | succ n ih =>
      obtain ⟨w⟩ := ih
      obtain ⟨v, hv⟩ := h (w.1 (Fin.last n))
      exact ⟨extendPath E n w v hv⟩




/-! ## Closed walks and periodic orbits -/








/-! ## Nonemptiness of the inverse limit -/




open LorenzLimit in
theorem solution[Fintype V] [Nonempty V] (h : NoDeadEnds E) (n : ℕ) :
    0 < Fintype.card (FinPath E n) :=
  @Fintype.card_pos _ _ (finPath_nonempty h n)
