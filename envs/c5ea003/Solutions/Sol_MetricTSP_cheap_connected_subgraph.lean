-- Prove2me | solution 1 for MetricTSP.cheap_connected_subgraph
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T19:56:42.115126+00:00
-- url     : https://prove2.me/submissions/cc21d062-5259-4b7c-82bc-70bd4ab92429

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_graph_cost

namespace MetricTSP

open Finset SimpleGraph

variable {n : ℕ}

lemma metric_nonneg'' {c : Fin n → Fin n → ℝ} (hc : IsMetricCost c) (u v : Fin n) :
    0 ≤ c u v := by
  obtain ⟨hsym, hdiag, htri⟩ := hc
  have h := htri u v u
  rw [hdiag u, hsym v u] at h
  linarith

lemma pairCost_nonneg' {c : Fin n → Fin n → ℝ} (hc0 : ∀ u v, 0 ≤ c u v)
    (e : Sym2 (Fin n)) : 0 ≤ pairCost c e := by
  induction e with
  | _ u v =>
    show (0 : ℝ) ≤ (c u v + c v u) / 2
    have h1 := hc0 u v
    have h2 := hc0 v u
    linarith

lemma pairCost_mk' {c : Fin n → Fin n → ℝ} (hsym : ∀ u v, c u v = c v u) (u v : Fin n) :
    pairCost c s(u, v) = c u v := by
  show (c u v + c v u) / 2 = c u v
  rw [hsym v u]
  ring

open Classical in
/-- The edge set of a graph as a `Finset`, with a fixed choice of instance. -/
noncomputable def edgeFin (G : SimpleGraph (Fin n)) : Finset (Sym2 (Fin n)) :=
  G.edgeSet.toFinset

lemma mem_edgeFin {G : SimpleGraph (Fin n)} {e : Sym2 (Fin n)} :
    e ∈ edgeFin G ↔ e ∈ G.edgeSet := by
  classical
  unfold edgeFin
  exact Set.mem_toFinset

/-- The cost of a finite set of unordered pairs. -/
noncomputable def fcost (c : Fin n → Fin n → ℝ) (t : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ e ∈ t, pairCost c e

lemma fcost_graphCost (c : Fin n → Fin n → ℝ) (G : SimpleGraph (Fin n)) :
    graphCost c G = fcost c (edgeFin G) := by
  classical
  unfold graphCost fcost
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext e
  rw [Set.mem_toFinset, mem_edgeFin]

/-- A minimum-cost spanning connected subgraph can be taken to be a tree, and it is
at most as expensive as every spanning connected edge set. -/
lemma exists_min_spanning_tree (hn : 1 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc0 : ∀ u v, 0 ≤ c u v) :
    ∃ TT : SimpleGraph (Fin n), TT.IsTree ∧
      ∀ t : Finset (Sym2 (Fin n)), (SimpleGraph.fromEdgeSet (↑t : Set (Sym2 (Fin n)))).Connected →
        fcost c (edgeFin TT) ≤ fcost c t := by
  classical
  have hne : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  set cand : Finset (Finset (Sym2 (Fin n))) :=
    univ.filter (fun t => (SimpleGraph.fromEdgeSet (↑t : Set (Sym2 (Fin n)))).Connected)
    with hcand
  have hcne : cand.Nonempty := by
    refine ⟨univ, ?_⟩
    rw [hcand, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hcoe : ((univ : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))) = Set.univ := by
      simp
    rw [hcoe, SimpleGraph.fromEdgeSet_univ]
    exact SimpleGraph.connected_top
  obtain ⟨t0, ht0, hmin0⟩ := Finset.exists_min_image cand (fcost c) hcne
  rw [hcand, Finset.mem_filter] at ht0
  obtain ⟨TT, hle, hTree⟩ := ht0.2.exists_isTree_le
  refine ⟨TT, hTree, ?_⟩
  intro t hconn
  have htc : t ∈ cand := by
    rw [hcand, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hconn⟩
  have h1 : fcost c (edgeFin TT) ≤ fcost c t0 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      rw [mem_edgeFin] at he
      have hmem := SimpleGraph.edgeSet_mono hle he
      rw [SimpleGraph.edgeSet_fromEdgeSet] at hmem
      simpa using hmem.1
    · intro e _ _
      exact pairCost_nonneg' hc0 e
  exact le_trans h1 (hmin0 t htc)

/-- The graph of all pairs of cost at most `d`. -/
noncomputable def cheapG (c : Fin n → Fin n → ℝ) (d : ℝ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e : Sym2 (Fin n) | pairCost c e ≤ d}

/-- The subgraph of `TT` consisting of its edges of cost at most `d`. -/
noncomputable def cheapT (TT : SimpleGraph (Fin n)) (c : Fin n → Fin n → ℝ) (d : ℝ) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (TT.edgeSet ∩ {e : Sym2 (Fin n) | pairCost c e ≤ d})

lemma cheapT_le (TT : SimpleGraph (Fin n)) (c : Fin n → Fin n → ℝ) (d : ℝ) :
    cheapT TT c d ≤ TT := by
  intro u v h
  rw [cheapT, SimpleGraph.fromEdgeSet_adj] at h
  exact h.1.1

lemma cheapT_le_cheapG (TT : SimpleGraph (Fin n)) (c : Fin n → Fin n → ℝ) (d : ℝ) :
    cheapT TT c d ≤ cheapG c d := by
  intro u v h
  rw [cheapT, SimpleGraph.fromEdgeSet_adj] at h
  rw [cheapG, SimpleGraph.fromEdgeSet_adj]
  exact ⟨h.1.2, h.2⟩

lemma cheapT_le_delete (TT : SimpleGraph (Fin n)) (c : Fin n → Fin n → ℝ) (d : ℝ)
    (f : Sym2 (Fin n)) (hf : d < pairCost c f) :
    cheapT TT c d ≤ TT.deleteEdges {f} := by
  intro u v h
  rw [cheapT, SimpleGraph.fromEdgeSet_adj] at h
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨h.1.1, ?_⟩
  intro hef
  rw [Set.mem_singleton_iff] at hef
  rw [hef] at h
  exact absurd h.1.2 (not_le.mpr hf)

/-- Along a path in `TT` toward `b`, either the start is already connected to `b` in a
subgraph `C ≤ TT`, or there is a first dart leaving the `C`-region of `a`, and the rest
of the path avoids that dart's edge. -/
lemma cross_aux (TT C : SimpleGraph (Fin n)) (a b : Fin n) :
    ∀ (z : Fin n) (W : TT.Walk z b), W.IsPath → C.Reachable a z →
      C.Reachable a b ∨
      ∃ p q : Fin n, TT.Adj p q ∧ C.Reachable a p ∧ ¬C.Reachable a q ∧
        (TT.deleteEdges {s(p, q)}).Reachable q b := by
  intro z W
  induction W with
  | nil =>
      intro _ hz
      exact Or.inl hz
  | @cons z y bb hadj W' ih =>
      intro hpath hz
      by_cases hy : C.Reachable a y
      · exact ih ((SimpleGraph.Walk.cons_isPath_iff hadj W').mp hpath).1 hy
      · refine Or.inr ⟨z, y, hadj, hz, hy, ?_⟩
        have hnotin : s(z, y) ∉ W'.edges := by
          intro hmem
          have hzsup : z ∈ W'.support :=
            SimpleGraph.Walk.fst_mem_support_of_mem_edges W' hmem
          exact ((SimpleGraph.Walk.cons_isPath_iff hadj W').mp hpath).2 hzsup
        refine ⟨SimpleGraph.Walk.toDeleteEdges {s(z, y)} W' ?_⟩
        intro e he
        rw [Set.mem_singleton_iff]
        intro heq
        rw [heq] at he
        exact hnotin he

/-- After deleting one edge `s(p,q)`, every vertex that could reach `zz` can still
reach `zz`, `p`, or `q`. -/
lemma delete_transfer (H : SimpleGraph (Fin n)) (p q : Fin n) :
    ∀ (z zz : Fin n), H.Walk z zz →
      (H.deleteEdges {s(p, q)}).Reachable z zz ∨
      (H.deleteEdges {s(p, q)}).Reachable z p ∨
      (H.deleteEdges {s(p, q)}).Reachable z q := by
  intro z zz W
  induction W with
  | nil => exact Or.inl (SimpleGraph.Reachable.refl _)
  | @cons z y bb hadj W' ih =>
      by_cases hef : s(z, y) = s(p, q)
      · rcases Sym2.eq_iff.mp hef with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl (SimpleGraph.Reachable.refl _))
        · exact Or.inr (Or.inr (SimpleGraph.Reachable.refl _))
      · have hadj' : (H.deleteEdges {s(p, q)}).Adj z y := by
          rw [SimpleGraph.deleteEdges_adj]
          refine ⟨hadj, ?_⟩
          intro hmem
          rw [Set.mem_singleton_iff] at hmem
          exact hef hmem
        rcases ih with h | h | h
        · exact Or.inl (hadj'.reachable.trans h)
        · exact Or.inr (Or.inl (hadj'.reachable.trans h))
        · exact Or.inr (Or.inr (hadj'.reachable.trans h))

/-- **Exchange argument.** In a minimum-cost spanning tree, the endpoints of a cheap
pair are already connected by cheap tree edges. -/
lemma cheap_span_adj (hn : 1 ≤ n) (c : Fin n → Fin n → ℝ) (hc0 : ∀ u v, 0 ≤ c u v)
    (TT : SimpleGraph (Fin n)) (hTree : TT.IsTree)
    (hmin : ∀ t : Finset (Sym2 (Fin n)),
      (SimpleGraph.fromEdgeSet (↑t : Set (Sym2 (Fin n)))).Connected →
      fcost c (edgeFin TT) ≤ fcost c t)
    (d : ℝ) {a b : Fin n} (hab : (cheapG c d).Adj a b) :
    (cheapT TT c d).Reachable a b := by
  classical
  by_contra hnr
  rw [cheapG, SimpleGraph.fromEdgeSet_adj] at hab
  obtain ⟨habc, habne⟩ := hab
  obtain ⟨P, hP⟩ := (hTree.connected.preconnected a b).exists_isPath
  rcases cross_aux TT (cheapT TT c d) a b a P hP (SimpleGraph.Reachable.refl a) with
    hreach | ⟨p, q, hpq, hap, hnaq, hqb⟩
  · exact hnr hreach
  set f : Sym2 (Fin n) := s(p, q) with hf
  have hfexp : d < pairCost c f := by
    by_contra h
    rw [not_lt] at h
    apply hnaq
    refine hap.trans (SimpleGraph.Adj.reachable ?_)
    rw [cheapT, SimpleGraph.fromEdgeSet_adj]
    exact ⟨⟨hpq, h⟩, hpq.ne⟩
  have hfT : f ∈ edgeFin TT := by
    rw [mem_edgeFin]
    exact hpq
  have habT : s(a, b) ∉ edgeFin TT := by
    rw [mem_edgeFin]
    intro hmem
    apply hnr
    apply SimpleGraph.Adj.reachable
    rw [cheapT, SimpleGraph.fromEdgeSet_adj]
    exact ⟨Set.mem_inter hmem habc, habne⟩
  set t' : Finset (Sym2 (Fin n)) := insert s(a, b) ((edgeFin TT).erase f) with ht'
  have hDle : TT.deleteEdges {f} ≤ SimpleGraph.fromEdgeSet (↑t' : Set (Sym2 (Fin n))) := by
    intro u v h
    rw [SimpleGraph.deleteEdges_adj] at h
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨?_, h.1.ne⟩
    rw [ht', Finset.coe_insert, Set.mem_insert_iff]
    right
    rw [Finset.mem_coe, Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro heq
      exact h.2 (by rw [heq]; exact Set.mem_singleton f)
    · rw [mem_edgeFin]
      exact h.1
  have habAdj : (SimpleGraph.fromEdgeSet (↑t' : Set (Sym2 (Fin n)))).Adj a b := by
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨?_, habne⟩
    rw [ht', Finset.coe_insert, Set.mem_insert_iff]
    left
    rfl
  have hcheapD : cheapT TT c d ≤ TT.deleteEdges {f} := cheapT_le_delete TT c d f hfexp
  have hap' : (SimpleGraph.fromEdgeSet (↑t' : Set (Sym2 (Fin n)))).Reachable a p :=
    (hap.mono hcheapD).mono hDle
  have hqb' : (SimpleGraph.fromEdgeSet (↑t' : Set (Sym2 (Fin n)))).Reachable q b :=
    hqb.mono hDle
  have hall : ∀ z, (SimpleGraph.fromEdgeSet (↑t' : Set (Sym2 (Fin n)))).Reachable z a := by
    intro z
    obtain ⟨Wz⟩ := hTree.connected.preconnected z a
    rcases delete_transfer TT p q z a Wz with h | h | h
    · exact h.mono hDle
    · exact (h.mono hDle).trans hap'.symm
    · exact (h.mono hDle).trans (hqb'.trans habAdj.symm.reachable)
  have hconn' : (SimpleGraph.fromEdgeSet (↑t' : Set (Sym2 (Fin n)))).Connected := by
    rw [SimpleGraph.connected_iff]
    exact ⟨fun u v => (hall u).trans (hall v).symm, ⟨a⟩⟩
  have hmin' := hmin t' hconn'
  have habE : s(a, b) ∉ (edgeFin TT).erase f :=
    fun h => habT (Finset.mem_of_mem_erase h)
  have hsum : fcost c t' = pairCost c s(a, b) + (fcost c (edgeFin TT) - pairCost c f) := by
    rw [ht']
    unfold fcost
    rw [Finset.sum_insert habE]
    congr 1
    have := Finset.sum_erase_add (edgeFin TT) (pairCost c) hfT
    linarith
  rw [hsum] at hmin'
  have hd : pairCost c s(a, b) ≤ d := habc
  linarith

/-- Full reachability version of the exchange property. -/
lemma cheap_span (hn : 1 ≤ n) (c : Fin n → Fin n → ℝ) (hc0 : ∀ u v, 0 ≤ c u v)
    (TT : SimpleGraph (Fin n)) (hTree : TT.IsTree)
    (hmin : ∀ t : Finset (Sym2 (Fin n)),
      (SimpleGraph.fromEdgeSet (↑t : Set (Sym2 (Fin n)))).Connected →
      fcost c (edgeFin TT) ≤ fcost c t)
    (d : ℝ) :
    ∀ (u v : Fin n), (cheapG c d).Reachable u v → (cheapT TT c d).Reachable u v := by
  have key : ∀ (u v : Fin n), (cheapG c d).Walk u v → (cheapT TT c d).Reachable u v := by
    intro u v W
    induction W with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons hadj W' ih =>
        exact (cheap_span_adj hn c hc0 TT hTree hmin d hadj).trans ih
  intro u v h
  obtain ⟨W⟩ := h
  exact key u v W

/-- Deleting a bridge strictly increases the number of connected components. -/
lemma card_comp_lt_of_bridge {H : SimpleGraph (Fin n)} {u v : Fin n}
    (hbr : H.IsBridge s(u, v)) :
    Nat.card H.ConnectedComponent < Nat.card (H.deleteEdges {s(u, v)}).ConnectedComponent := by
  classical
  rw [SimpleGraph.isBridge_iff] at hbr
  obtain ⟨hadj, hnreach⟩ := hbr
  set D := H.deleteEdges {s(u, v)} with hD
  have hle : D ≤ H := SimpleGraph.deleteEdges_le _
  set ψ : D.ConnectedComponent → H.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE hle) with hψ
  have hsurj : Function.Surjective ψ :=
    SimpleGraph.ConnectedComponent.surjective_map_ofLE hle
  have hle_card : Nat.card H.ConnectedComponent ≤ Nat.card D.ConnectedComponent :=
    Nat.card_le_card_of_surjective ψ hsurj
  rcases lt_or_eq_of_le hle_card with h | h
  · exact h
  exfalso
  -- equal cardinalities force ψ bijective, hence injective — contradicting the bridge
  have hbij : Function.Bijective ψ :=
    hsurj.bijective_of_nat_card_le (le_of_eq h.symm)
  have h1 : ψ (D.connectedComponentMk u) = ψ (D.connectedComponentMk v) := by
    rw [hψ]
    rw [SimpleGraph.ConnectedComponent.map_mk, SimpleGraph.ConnectedComponent.map_mk]
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj (by exact hadj)
  have h2 := hbij.injective h1
  rw [SimpleGraph.ConnectedComponent.eq] at h2
  exact hnreach h2

/-- Deleting `j` edges of an acyclic graph creates at least `j` new components. -/
lemma comps_ge_of_acyclic (TT : SimpleGraph (Fin n)) (hac : TT.IsAcyclic) :
    ∀ (E : Finset (Sym2 (Fin n))), (↑E : Set (Sym2 (Fin n))) ⊆ TT.edgeSet →
      E.card + Nat.card TT.ConnectedComponent
        ≤ Nat.card (TT.deleteEdges (↑E : Set (Sym2 (Fin n)))).ConnectedComponent := by
  classical
  intro E
  induction E using Finset.induction_on with
  | empty =>
      intro _
      simp [SimpleGraph.deleteEdges_empty]
  | @insert f E hfE ih =>
      intro hsub
      have hEsub : (↑E : Set (Sym2 (Fin n))) ⊆ TT.edgeSet := by
        intro e he
        exact hsub (by simpa using Or.inr he)
      have hfmem : f ∈ TT.edgeSet := hsub (by simp)
      set H := TT.deleteEdges (↑E : Set (Sym2 (Fin n))) with hH
      have hHle : H ≤ TT := SimpleGraph.deleteEdges_le _
      have hHac : H.IsAcyclic := hac.anti hHle
      have hfH : f ∈ H.edgeSet := by
        rw [hH, SimpleGraph.edgeSet_deleteEdges]
        exact ⟨hfmem, by simpa using hfE⟩
      obtain ⟨u, v⟩ := f
      have hbr : H.IsBridge s(u, v) :=
        SimpleGraph.isAcyclic_iff_forall_edge_isBridge.mp hHac hfH
      have hstep := card_comp_lt_of_bridge hbr
      have hins : TT.deleteEdges (↑(insert s(u, v) E) : Set (Sym2 (Fin n)))
          = H.deleteEdges {s(u, v)} := by
        rw [hH, SimpleGraph.deleteEdges_deleteEdges]
        congr 1
        ext e
        simp [or_comm]
      rw [hins, Finset.card_insert_of_notMem hfE]
      have := ih hEsub
      omega

/-- The chain: expensive tree edges at level `dd` number at most (number of components of
the cheap graph) minus one. -/
lemma tree_expensive_count (hn : 1 ≤ n) (c : Fin n → Fin n → ℝ) (hc0 : ∀ u v, 0 ≤ c u v)
    (TT : SimpleGraph (Fin n)) (hTree : TT.IsTree)
    (hmin : ∀ t : Finset (Sym2 (Fin n)),
      (SimpleGraph.fromEdgeSet (↑t : Set (Sym2 (Fin n)))).Connected →
      fcost c (edgeFin TT) ≤ fcost c t)
    (dd : ℝ) :
    ((edgeFin TT).filter (fun e => dd < pairCost c e)).card + 1
      ≤ Nat.card ((cheapG c dd).ConnectedComponent) := by
  classical
  set E := (edgeFin TT).filter (fun e => dd < pairCost c e) with hE
  have hdel : TT.deleteEdges (↑E : Set (Sym2 (Fin n))) = cheapT TT c dd := by
    ext u v
    rw [SimpleGraph.deleteEdges_adj, cheapT, SimpleGraph.fromEdgeSet_adj]
    constructor
    · rintro ⟨hadj, hnE⟩
      refine ⟨⟨hadj, ?_⟩, hadj.ne⟩
      by_contra hexp
      apply hnE
      rw [Finset.mem_coe, hE, Finset.mem_filter]
      exact ⟨mem_edgeFin.mpr hadj, lt_of_not_ge hexp⟩
    · rintro ⟨⟨hadj, hcheap⟩, _⟩
      refine ⟨hadj, ?_⟩
      intro hmem
      rw [Finset.mem_coe, hE, Finset.mem_filter] at hmem
      exact absurd hcheap (not_le.mpr hmem.2)
  have hsub : (↑E : Set (Sym2 (Fin n))) ⊆ TT.edgeSet := by
    intro e he
    rw [Finset.mem_coe, hE, Finset.mem_filter, mem_edgeFin] at he
    exact he.1
  have hcomps := comps_ge_of_acyclic TT hTree.isAcyclic E hsub
  rw [hdel] at hcomps
  have hone : Nat.card TT.ConnectedComponent = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨hTree.connected.preconnected.subsingleton_connectedComponent, ?_⟩
    exact ⟨TT.connectedComponentMk ⟨0, by omega⟩⟩
  have hequiv : (cheapT TT c dd).ConnectedComponent ≃ (cheapG c dd).ConnectedComponent :=
    Quot.congrRight (fun a b =>
      ⟨fun h => h.mono (cheapT_le_cheapG TT c dd), cheap_span hn c hc0 TT hTree hmin dd a b⟩)
  have hcard := Nat.card_congr hequiv
  omega

open Classical in
/-- The Held–Karp mass of the cheap pairs, bounded through the components of the
cheap graph: at most `2n - 2k` when there are `k ≥ 2` components. -/
lemma cheap_mass (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) (d : ℝ)
    (hk : 2 ≤ Nat.card ((cheapG c d).ConnectedComponent)) :
    ∑ u, ∑ v, (if (cheapG c d).Adj u v then x u v else 0)
      ≤ 2 * n - 2 * Nat.card ((cheapG c d).ConnectedComponent) := by
  classical
  obtain ⟨hxsym, hxdiag, hxnn, hxle, hxdeg, hxcut⟩ := hx
  letI : Fintype ((cheapG c d).ConnectedComponent) := Fintype.ofFinite _
  set comp : Fin n → (cheapG c d).ConnectedComponent :=
    (cheapG c d).connectedComponentMk with hcomp
  set fib : (cheapG c d).ConnectedComponent → Finset (Fin n) :=
    fun C => univ.filter (fun v => comp v = C) with hfib
  have hcompadj : ∀ {u v : Fin n}, (cheapG c d).Adj u v → comp u = comp v := by
    intro u v h
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h
  -- group the double sum by the component of the first coordinate
  have hgroup : ∑ u, ∑ v, (if (cheapG c d).Adj u v then x u v else 0)
      = ∑ C : (cheapG c d).ConnectedComponent, ∑ u ∈ fib C,
          ∑ v, (if (cheapG c d).Adj u v then x u v else 0) := by
    rw [Finset.sum_fiberwise_of_maps_to (fun u _ => Finset.mem_univ (comp u))]
  rw [hgroup]
  -- inside a component, the cheap mass is at most the within-component mass
  have hinner : ∀ C : (cheapG c d).ConnectedComponent, ∀ u ∈ fib C,
      ∑ v, (if (cheapG c d).Adj u v then x u v else 0) ≤ ∑ v ∈ fib C, x u v := by
    intro C u hu
    rw [hfib, Finset.mem_filter] at hu
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro v hv
      rw [Finset.mem_filter] at hv
      rw [hfib, Finset.mem_filter]
      exact ⟨Finset.mem_univ v, (hcompadj hv.2).symm.trans hu.2⟩
    · intro v _ _
      exact hxnn u v
  -- within-component mass via degrees and the cut constraint
  have hwithin : ∀ C : (cheapG c d).ConnectedComponent,
      ∑ u ∈ fib C, ∑ v ∈ fib C, x u v ≤ 2 * (fib C).card - 2 := by
    intro C
    have hCne : (fib C).Nonempty := by
      obtain ⟨v, rfl⟩ := C.exists_rep
      exact ⟨v, by rw [hfib, Finset.mem_filter]; exact ⟨Finset.mem_univ v, rfl⟩⟩
    have hCproper : fib C ≠ univ := by
      intro hcontra
      obtain ⟨C', hC'⟩ := Fintype.exists_ne_of_one_lt_card
        (by
          rw [← Nat.card_eq_fintype_card]
          omega) C
      obtain ⟨v', rfl⟩ := C'.exists_rep
      have : v' ∈ fib C := hcontra ▸ Finset.mem_univ v'
      rw [hfib, Finset.mem_filter] at this
      exact hC' this.2
    have hdegsum : ∑ u ∈ fib C, ∑ v, x u v = 2 * (fib C).card := by
      rw [Finset.sum_congr rfl (fun u _ => hxdeg u)]
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    have hsplit : ∀ u : Fin n, ∑ v ∈ fib C, x u v + ∑ v ∈ (fib C)ᶜ, x u v = ∑ v, x u v :=
      fun u => Finset.sum_add_sum_compl (fib C) (x u)
    have hcut := hxcut (fib C) hCne hCproper
    have h1 : ∑ u ∈ fib C, ∑ v ∈ fib C, x u v
        = 2 * (fib C).card - ∑ u ∈ fib C, ∑ v ∈ (fib C)ᶜ, x u v := by
      have h2 : ∑ u ∈ fib C, (∑ v ∈ fib C, x u v + ∑ v ∈ (fib C)ᶜ, x u v)
          = 2 * (fib C).card := by
        rw [Finset.sum_congr rfl (fun u _ => hsplit u)]
        exact hdegsum
      rw [Finset.sum_add_distrib] at h2
      linarith
    rw [h1]
    linarith
  calc ∑ C : (cheapG c d).ConnectedComponent, ∑ u ∈ fib C,
        ∑ v, (if (cheapG c d).Adj u v then x u v else 0)
      ≤ ∑ C : (cheapG c d).ConnectedComponent, ∑ u ∈ fib C, ∑ v ∈ fib C, x u v := by
        apply Finset.sum_le_sum
        intro C _
        exact Finset.sum_le_sum (hinner C)
    _ ≤ ∑ C : (cheapG c d).ConnectedComponent, (2 * ((fib C).card : ℝ) - 2) :=
        Finset.sum_le_sum (fun C _ => hwithin C)
    _ = 2 * n - 2 * Nat.card ((cheapG c d).ConnectedComponent) := by
        rw [Finset.sum_sub_distrib]
        rw [← Finset.mul_sum]
        have hcards : ∑ C : (cheapG c d).ConnectedComponent, ((fib C).card : ℝ) = n := by
          have := Finset.card_eq_sum_card_fiberwise
            (f := comp) (s := univ) (t := univ) (fun u _ => Finset.mem_univ (comp u))
          have hcast := congrArg (fun m : ℕ => (m : ℝ)) this
          push_cast at hcast
          rw [← hcast]
          simp
        rw [hcards, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
        simp [nsmul_eq_mul]
        ring


/-- The next value of `D` strictly above `v`, or `v` itself if there is none. -/
noncomputable def nextD (D : Finset ℝ) (v : ℝ) : ℝ :=
  if h : (D.filter (fun d' => v < d')).Nonempty then (D.filter (fun d' => v < d')).min' h else v

lemma nextD_ge (D : Finset ℝ) (v : ℝ) : v ≤ nextD D v := by
  unfold nextD
  split_ifs with h
  · have hmem := Finset.min'_mem _ h
    rw [Finset.mem_filter] at hmem
    exact le_of_lt hmem.2
  · exact le_refl v

/-- Discrete layer-cake: every nonnegative element of `D` is the sum of the gaps of `D`
below it. -/
lemma telescope (D : Finset ℝ) (h0 : (0:ℝ) ∈ D) (hDpos : ∀ d ∈ D, 0 ≤ d) :
    ∀ (N : ℕ) (v : ℝ), v ∈ D → 0 ≤ v → (D.filter (fun dd => dd < v)).card ≤ N →
      v = ∑ dd ∈ D.filter (fun dd => dd < v), (nextD D dd - dd) := by
  classical
  intro N
  induction N with
  | zero =>
      intro v hv hv0 hcard
      have hempty : D.filter (fun dd => dd < v) = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_antisymm hcard (Nat.zero_le _))
      have hv0' : v = 0 := by
        by_contra hne
        have hpos : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hne)
        have hin : (0:ℝ) ∈ D.filter (fun dd => dd < v) := Finset.mem_filter.mpr ⟨h0, hpos⟩
        rw [hempty] at hin
        exact Finset.notMem_empty _ hin
      rw [hempty, hv0']
      simp
  | succ N ih =>
      intro v hv hv0 hcard
      by_cases hne : (D.filter (fun dd => dd < v)).Nonempty
      · set M := (D.filter (fun dd => dd < v)).max' hne with hM
        have hMmem := Finset.max'_mem _ hne
        rw [Finset.mem_filter] at hMmem
        obtain ⟨hMD, hMv⟩ := hMmem
        have hM0 : 0 ≤ M := hDpos M hMD
        have hnext : nextD D M = v := by
          have hfne : (D.filter (fun d' => M < d')).Nonempty :=
            ⟨v, Finset.mem_filter.mpr ⟨hv, hMv⟩⟩
          unfold nextD
          rw [dif_pos hfne]
          apply le_antisymm
          · exact Finset.min'_le _ v (Finset.mem_filter.mpr ⟨hv, hMv⟩)
          · apply Finset.le_min'
            intro y hy
            rw [Finset.mem_filter] at hy
            by_contra hyv
            push_neg at hyv
            have hyf : y ∈ D.filter (fun dd => dd < v) := Finset.mem_filter.mpr ⟨hy.1, hyv⟩
            have := Finset.le_max' _ y hyf
            exact absurd hy.2 (not_lt.mpr this)
        have hins : D.filter (fun dd => dd < v) = insert M (D.filter (fun dd => dd < M)) := by
          ext dd
          rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_filter]
          constructor
          · rintro ⟨hdD, hdv⟩
            by_cases hdM : dd = M
            · exact Or.inl hdM
            · right
              refine ⟨hdD, ?_⟩
              have hle := Finset.le_max' (D.filter (fun dd => dd < v)) dd
                (Finset.mem_filter.mpr ⟨hdD, hdv⟩)
              exact lt_of_le_of_ne hle hdM
          · rintro (rfl | ⟨hdD, hdM⟩)
            · exact ⟨hMD, hMv⟩
            · exact ⟨hdD, lt_trans hdM hMv⟩
        have hMnotin : M ∉ D.filter (fun dd => dd < M) := by
          intro h
          rw [Finset.mem_filter] at h
          exact lt_irrefl M h.2
        have hcard' : (D.filter (fun dd => dd < M)).card ≤ N := by
          have hc2 : (insert M (D.filter (fun dd => dd < M))).card ≤ N + 1 := hins ▸ hcard
          rw [Finset.card_insert_of_notMem hMnotin] at hc2
          omega
        have hMtel := ih M hMD hM0 hcard'
        rw [hins, Finset.sum_insert hMnotin, hnext, ← hMtel]
        ring
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        have hv0' : v = 0 := by
          by_contra hvne
          have hpos : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hvne)
          have hin : (0:ℝ) ∈ D.filter (fun dd => dd < v) := Finset.mem_filter.mpr ⟨h0, hpos⟩
          rw [hne] at hin
          exact Finset.notMem_empty _ hin
        rw [hne, hv0']
        simp

open Classical in
/-- **A cheap connected subgraph from any Held–Karp point** — the fractional tree bound:
the minimum spanning tree costs at most the Held–Karp objective. -/
theorem cheap_connected_of_feasible_aux (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) :
    ∃ G : SimpleGraph (Fin n), G.Connected ∧
      graphCost c G ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hc0 := metric_nonneg'' hc
  have hxnn : ∀ u v, 0 ≤ x u v := hx.2.2.1
  have hxdeg : ∀ v, ∑ u, x v u = 2 := hx.2.2.2.2.1
  obtain ⟨TT, hTree, hmin⟩ := exists_min_spanning_tree hn1 c hc0
  refine ⟨TT, hTree.connected, ?_⟩
  rw [fcost_graphCost]
  set D : Finset ℝ := insert 0 (Finset.image (fun p : Fin n × Fin n => c p.1 p.2) univ)
    with hD
  have h0D : (0:ℝ) ∈ D := Finset.mem_insert_self 0 _
  have hDpos : ∀ dd ∈ D, 0 ≤ dd := by
    intro dd hdd
    rw [hD, Finset.mem_insert] at hdd
    rcases hdd with rfl | hdd
    · exact le_refl 0
    · obtain ⟨pp, _, rfl⟩ := Finset.mem_image.mp hdd
      exact hc0 pp.1 pp.2
  have hcD : ∀ u v : Fin n, c u v ∈ D := fun u v =>
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(u, v), Finset.mem_univ _, rfl⟩)
  have hpairD : ∀ e : Sym2 (Fin n), pairCost c e ∈ D := by
    intro e
    induction e with
    | _ u v =>
        rw [pairCost_mk' hc.1]
        exact hcD u v
  have htree_expand : fcost c (edgeFin TT)
      = ∑ dd ∈ D, (nextD D dd - dd) *
          (((edgeFin TT).filter (fun e => dd < pairCost c e)).card : ℝ) := by
    unfold fcost
    calc ∑ e ∈ edgeFin TT, pairCost c e
        = ∑ e ∈ edgeFin TT,
            ∑ dd ∈ D.filter (fun dd => dd < pairCost c e), (nextD D dd - dd) := by
          apply Finset.sum_congr rfl
          intro e _
          exact telescope D h0D hDpos D.card (pairCost c e) (hpairD e)
            (pairCost_nonneg' hc0 e) (Finset.card_filter_le _ _)
      _ = ∑ e ∈ edgeFin TT, ∑ dd ∈ D,
            (if dd < pairCost c e then nextD D dd - dd else 0) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.sum_filter]
      _ = ∑ dd ∈ D, ∑ e ∈ edgeFin TT,
            (if dd < pairCost c e then nextD D dd - dd else 0) := Finset.sum_comm
      _ = ∑ dd ∈ D, (nextD D dd - dd) *
            (((edgeFin TT).filter (fun e => dd < pairCost c e)).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro dd _
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          ring
  have hswap : ∀ (F : Fin n → Fin n → ℝ → ℝ),
      ∑ u, ∑ v, ∑ dd ∈ D, F u v dd = ∑ dd ∈ D, ∑ u, ∑ v, F u v dd := by
    intro F
    calc ∑ u, ∑ v, ∑ dd ∈ D, F u v dd
        = ∑ u, ∑ dd ∈ D, ∑ v, F u v dd :=
          Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = ∑ dd ∈ D, ∑ u, ∑ v, F u v dd := Finset.sum_comm
  have hobj_expand : ∑ u, ∑ v, c u v * x u v
      = ∑ dd ∈ D, (nextD D dd - dd) *
          (∑ u, ∑ v, (if dd < c u v then x u v else 0)) := by
    calc ∑ u, ∑ v, c u v * x u v
        = ∑ u, ∑ v, ∑ dd ∈ D,
            (if dd < c u v then (nextD D dd - dd) * x u v else 0) := by
          apply Finset.sum_congr rfl; intro u _
          apply Finset.sum_congr rfl; intro v _
          have hcv := telescope D h0D hDpos D.card (c u v) (hcD u v) (hc0 u v)
            (Finset.card_filter_le _ _)
          calc c u v * x u v
              = (∑ dd ∈ D.filter (fun dd => dd < c u v), (nextD D dd - dd)) * x u v := by
                rw [← hcv]
            _ = ∑ dd ∈ D.filter (fun dd => dd < c u v), (nextD D dd - dd) * x u v := by
                rw [Finset.sum_mul]
            _ = ∑ dd ∈ D, (if dd < c u v then (nextD D dd - dd) * x u v else 0) := by
                rw [Finset.sum_filter]
      _ = ∑ dd ∈ D, ∑ u, ∑ v,
            (if dd < c u v then (nextD D dd - dd) * x u v else 0) :=
          hswap _
      _ = ∑ dd ∈ D, (nextD D dd - dd) *
            (∑ u, ∑ v, (if dd < c u v then x u v else 0)) := by
          apply Finset.sum_congr rfl
          intro dd _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro u _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro v _
          rw [mul_ite, mul_zero]
  have hperdd : ∀ dd ∈ D, (nextD D dd - dd) *
      (((edgeFin TT).filter (fun e => dd < pairCost c e)).card : ℝ)
      ≤ (nextD D dd - dd) * (((n:ℝ)-1)/n *
          ((1:ℝ)/2 * ∑ u, ∑ v, (if dd < c u v then x u v else 0))) := by
    intro dd hdd
    have hΔ : 0 ≤ nextD D dd - dd := by
      have := nextD_ge D dd
      linarith
    apply mul_le_mul_of_nonneg_left _ hΔ
    set k := Nat.card ((cheapG c dd).ConnectedComponent) with hkdef
    have hcount := tree_expensive_count hn1 c hc0 TT hTree hmin dd
    set Y := ∑ u, ∑ v, (if dd < c u v then x u v else 0) with hYdef
    have hYnn : 0 ≤ Y := by
      rw [hYdef]
      apply Finset.sum_nonneg; intro u _
      apply Finset.sum_nonneg; intro v _
      split_ifs
      · exact hxnn u v
      · exact le_refl 0
    have hnpos : (0:ℝ) < n := by
      have : (3:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hfracnn : (0:ℝ) ≤ ((n:ℝ)-1)/n := by
      apply div_nonneg _ (le_of_lt hnpos)
      have : (3:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hkn : k ≤ n := by
      have hsurj : Function.Surjective ((cheapG c dd).connectedComponentMk) :=
        fun C => C.exists_rep
      have hle := Nat.card_le_card_of_surjective _ hsurj
      rw [hkdef]
      calc Nat.card ((cheapG c dd).ConnectedComponent) ≤ Nat.card (Fin n) := hle
        _ = n := by simp
    by_cases hk2 : 2 ≤ k
    · have hcm := cheap_mass hn c x hx dd hk2
      have htotal : ∑ u : Fin n, ∑ v : Fin n, x u v = 2 * n := by
        rw [Finset.sum_congr rfl (fun u (_ : u ∈ univ) => hxdeg u)]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      have hcompl : ∀ u v : Fin n, (if dd < c u v then x u v else 0)
          = x u v - (if (cheapG c dd).Adj u v then x u v else 0) := by
        intro u v
        by_cases huv : u = v
        · subst huv
          have hxd : x u u = 0 := hx.2.1 u
          have hadj : ¬(cheapG c dd).Adj u u := SimpleGraph.irrefl _
          have hcd : ¬(dd < c u u) := by
            rw [hc.2.1 u]
            exact not_lt.mpr (hDpos dd hdd)
          rw [if_neg hcd, if_neg hadj, hxd]
          ring
        · have hadj_iff : (cheapG c dd).Adj u v ↔ c u v ≤ dd := by
            rw [cheapG, SimpleGraph.fromEdgeSet_adj]
            constructor
            · rintro ⟨hm, _⟩
              rwa [Set.mem_setOf_eq, pairCost_mk' hc.1] at hm
            · intro hle
              refine ⟨?_, huv⟩
              rw [Set.mem_setOf_eq, pairCost_mk' hc.1]
              exact hle
          by_cases hcle : c u v ≤ dd
          · rw [if_neg (not_lt.mpr hcle), if_pos (hadj_iff.mpr hcle)]
            ring
          · rw [if_pos (lt_of_not_ge hcle), if_neg (fun h => hcle (hadj_iff.mp h))]
            ring
      have hYeq : Y = 2*(n:ℝ) - ∑ u, ∑ v, (if (cheapG c dd).Adj u v then x u v else 0) := by
        rw [hYdef]
        rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) =>
          Finset.sum_congr rfl fun v (_ : v ∈ univ) => hcompl u v]
        have e1 : ∀ u : Fin n, ∑ v, (x u v - (if (cheapG c dd).Adj u v then x u v else 0))
            = (∑ v, x u v) - ∑ v, (if (cheapG c dd).Adj u v then x u v else 0) :=
          fun u => by rw [Finset.sum_sub_distrib]
        rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => e1 u, Finset.sum_sub_distrib,
          htotal]
      have hY2k : 2*(k:ℝ) ≤ Y := by
        rw [hYeq]
        have hcast : ((k:ℕ):ℝ) = (Nat.card ((cheapG c dd).ConnectedComponent) : ℝ) := by
          rw [hkdef]
        have := hcm
        linarith
      have hc1 : (((edgeFin TT).filter (fun e => dd < pairCost c e)).card : ℝ) ≤ (k:ℝ) - 1 := by
        have : ((edgeFin TT).filter (fun e => dd < pairCost c e)).card + 1 ≤ k := hcount
        have hcast : (((edgeFin TT).filter (fun e => dd < pairCost c e)).card + 1 : ℝ) ≤ (k:ℝ) := by
          exact_mod_cast this
        push_cast at hcast
        linarith
      have hfrac : ((k:ℝ) - 1) ≤ ((n:ℝ)-1)/n * k := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hnpos]
        have hknR : (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast hkn
        nlinarith
      calc (((edgeFin TT).filter (fun e => dd < pairCost c e)).card : ℝ)
          ≤ (k:ℝ) - 1 := hc1
        _ ≤ ((n:ℝ)-1)/n * k := hfrac
        _ ≤ ((n:ℝ)-1)/n * ((1:ℝ)/2 * Y) := by
            apply mul_le_mul_of_nonneg_left _ hfracnn
            linarith
    · have hcount0 : ((edgeFin TT).filter (fun e => dd < pairCost c e)).card = 0 := by
        omega
      rw [hcount0]
      push_cast
      apply mul_nonneg hfracnn
      linarith
  have hobj_nn : 0 ≤ ∑ u, ∑ v, c u v * x u v := by
    apply Finset.sum_nonneg; intro u _
    apply Finset.sum_nonneg; intro v _
    exact mul_nonneg (hc0 u v) (hxnn u v)
  have hnpos : (0:ℝ) < n := by
    have : (3:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  calc fcost c (edgeFin TT)
      = ∑ dd ∈ D, (nextD D dd - dd) *
          (((edgeFin TT).filter (fun e => dd < pairCost c e)).card : ℝ) := htree_expand
    _ ≤ ∑ dd ∈ D, (nextD D dd - dd) * (((n:ℝ)-1)/n *
          ((1:ℝ)/2 * ∑ u, ∑ v, (if dd < c u v then x u v else 0))) :=
        Finset.sum_le_sum hperdd
    _ = ((n:ℝ)-1)/n * ((1:ℝ)/2 * ∑ u, ∑ v, c u v * x u v) := by
        rw [hobj_expand, Finset.mul_sum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro dd _
        ring
    _ ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v := by
        have hf1 : ((n:ℝ)-1)/n ≤ 1 := by
          rw [div_le_one hnpos]
          linarith
        nlinarith


end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) :
    ∃ G : SimpleGraph (Fin n), G.Connected ∧
      graphCost c G ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v :=
  MetricTSP.cheap_connected_of_feasible_aux n hn c hc x hx

