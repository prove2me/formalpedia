-- Prove2me | solution 1 for Hadwiger.colorable_two_of_isAcyclic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:32:39.188674+00:00
-- url     : https://prove2.me/submissions/db2617dd-d051-4e39-8440-454ec01b028a

-- Sol generated from Probability/HadwigerBipartite.lean
import Mathlib
import Definitions.Def_Probability_HadwigerBipartite
/-
  Forests are Bipartite: the Colouring Half of Hadwiger's Conjecture for k = 2
  ===========================================================================

  Hadwiger's conjecture for `k = 2` says that a graph needing three colours has
  `K₃` as a minor; contrapositively, a graph with **no** `K₃` minor — that is, a
  forest — is `2`-colourable.  Mathlib knows that bipartite graphs have no odd
  cycles only as a `TODO`, so this file proves the colouring statement from
  scratch:

  * `Hadwiger.colorable_two_of_isAcyclic` : every finite acyclic graph is
                                            `2`-colourable.

  The proof is a genuine induction on the number of edges using the fact
  (`SimpleGraph.isAcyclic_iff_forall_adj_isBridge`) that *every* edge of a forest
  is a bridge: deleting an edge `uv` splits `u` from `v`, so a `2`-colouring of
  the smaller forest can be repaired by flipping the colours on the whole
  connected component of `v`.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): forests are 2-colourable, and the cleanest formal
    route avoids "leaf extraction" (which needs a degree count and a change of
    vertex type) in favour of edge deletion at constant vertex type.
  Experiment (Experimenter): deleting an arbitrary edge `uv` of an acyclic `G`
    leaves an acyclic `G'` with strictly fewer edges; the inductive colouring `C`
    of `G'` may accidentally satisfy `C u = C v`, so the repair step flips the
    colour on `{x | G'.Reachable v x}`.  Flipping on a whole component preserves
    properness because both endpoints of a `G'`-edge are reachable from `v` or
    neither is.
  Analysis (Analyst): the bridge property `¬ G'.Reachable u v` is exactly what
    makes the flip fix the offending edge without breaking anything else — this
    is where acyclicity enters, and it is the only place.
  Critique (Critic): the induction is on `Set.ncard G.edgeSet`, which needs
    finiteness of `V`; the statement is therefore given for `[Finite V]`.  For
    infinite forests 2-colourability still holds (De Bruijn–Erdős) but that is a
    compactness argument outside the present scope.
  Synthesis (PI): together with `HadwigerK3.lean` (cycle ⇒ `K₃` minor) this
    yields Hadwiger's conjecture for `k = 2`.
  -- !-- Lab Notes -- !--
-/

open Hadwiger

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}


@[simp] theorem flip2_ne (a : Fin 2) : flip2 a ≠ a := by
  fin_cases a <;> decide

theorem flip2_ne_flip2 {a b : Fin 2} (h : a ≠ b) : flip2 a ≠ flip2 b := by
  fin_cases a <;> fin_cases b <;> simp_all [flip2]

/-- A graph without edges is `2`-colourable. -/
theorem colorable_two_of_no_adj (h : ∀ x y : V, ¬ G.Adj x y) : G.Colorable 2 :=
  ⟨Coloring.mk (fun _ => 0) (fun {x y} hxy => absurd hxy (h x y))⟩

/-- Deleting one edge from an acyclic graph keeps it acyclic and removes exactly
that edge. -/
private theorem deleteEdge_le (G : SimpleGraph V) (e : Sym2 V) :
    G \ fromEdgeSet {e} ≤ G := fun _ _ h => h.1



open Hadwiger in
theorem solution[Finite V] {G : SimpleGraph V}
    (h : G.IsAcyclic) : G.Colorable 2 := by
  classical
  have key : ∀ n : ℕ, ∀ G : SimpleGraph V, G.edgeSet.ncard ≤ n → G.IsAcyclic → G.Colorable 2 := by
    intro n
    induction n with
    | zero =>
      intro G hcard _
      refine colorable_two_of_no_adj ?_
      intro x y hxy
      have hmem : s(x, y) ∈ G.edgeSet := hxy
      have hfin : G.edgeSet.Finite := Set.toFinite _
      have : 0 < G.edgeSet.ncard := Set.ncard_pos hfin |>.mpr ⟨_, hmem⟩
      omega
    | succ n ih =>
      intro G hcard hacyc
      by_cases hE : ∃ u v, G.Adj u v
      · obtain ⟨u, v, huv⟩ := hE
        set G' : SimpleGraph V := G \ fromEdgeSet {s(u, v)} with hG'def
        have hle : G' ≤ G := deleteEdge_le G _
        have hacyc' : G'.IsAcyclic := hacyc.anti hle
        -- the deleted edge really disappears
        have hnotmem : s(u, v) ∉ G'.edgeSet := by
          simp [hG'def]
        have hsub : G'.edgeSet ⊂ G.edgeSet := by
          refine ⟨edgeSet_mono hle, ?_⟩
          intro hcon
          exact hnotmem (hcon huv)
        have hcard' : G'.edgeSet.ncard ≤ n := by
          have hfin : G.edgeSet.Finite := Set.toFinite _
          have := Set.ncard_lt_ncard hsub hfin
          omega
        obtain ⟨C⟩ := ih G' hcard' hacyc'
        -- the bridge property of the deleted edge
        have hbridge : ¬ G'.Reachable u v := by
          have := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hacyc) huv
          exact (SimpleGraph.isBridge_iff.mp this).2
        -- edges other than `uv` survive in `G'`
        have hother : ∀ ⦃x y : V⦄, G.Adj x y → s(x, y) ≠ s(u, v) → G'.Adj x y := by
          intro x y hxy hne
          refine ⟨hxy, ?_⟩
          simp only [fromEdgeSet_adj, Set.mem_singleton_iff, not_and]
          exact fun hcon _ => hne hcon
        by_cases hCuv : C u = C v
        · -- repair by flipping the colours on the component of `v`
          refine ⟨Coloring.mk (fun x => if G'.Reachable v x then flip2 (C x) else C x) ?_⟩
          intro x y hxy
          by_cases hedge : s(x, y) = s(u, v)
          · -- the deleted edge itself (in either orientation)
            have hvv : G'.Reachable v v := Reachable.refl v
            have hvu : ¬ G'.Reachable v u := fun hr => hbridge hr.symm
            rcases Sym2.eq_iff.mp hedge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              simp only [if_neg hvu, if_pos hvv, hCuv] <;>
              first
                | exact fun hcon => flip2_ne _ hcon.symm
                | exact fun hcon => flip2_ne _ hcon
          · have hxy' : G'.Adj x y := hother hxy hedge
            have hC : C x ≠ C y := C.valid hxy'
            have hreach : G'.Reachable v x ↔ G'.Reachable v y :=
              ⟨fun hr => hr.trans hxy'.reachable, fun hr => hr.trans hxy'.symm.reachable⟩
            by_cases hvx : G'.Reachable v x
            · have hvy : G'.Reachable v y := hreach.mp hvx
              simpa [hvx, hvy] using flip2_ne_flip2 hC
            · have hvy : ¬ G'.Reachable v y := fun hr => hvx (hreach.mpr hr)
              simpa [hvx, hvy] using hC
        · -- the inductive colouring already works
          refine ⟨Coloring.mk C ?_⟩
          intro x y hxy
          by_cases hedge : s(x, y) = s(u, v)
          · rcases Sym2.eq_iff.mp hedge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hCuv
            · exact fun hcon => hCuv hcon.symm
          · exact C.valid (hother hxy hedge)
      · push_neg at hE
        exact colorable_two_of_no_adj hE
  exact key G.edgeSet.ncard G le_rfl h
