-- Prove2me | solution 1 for SimpleGraph.Walk.IsEulerianCircuit.even_degree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:43:29.604006+00:00
-- url     : https://prove2.me/submissions/bad89bf3-7679-404b-a8c4-0bcbd36fb90a

-- Sol generated from Bridges/GraphTheory/Eulerian.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_Eulerian
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Eulerian Circuits and the Degree Parity Condition

This file defines **Eulerian circuits** for simple graphs and proves
the fundamental necessary condition: if a graph has an Eulerian circuit,
then every vertex has even degree.

This is one of the oldest theorems in graph theory, dating back to
Euler's 1736 solution of the Königsberg Bridge Problem.

## Main Results

* `IsEulerianCircuit` — A circuit that traverses every edge exactly once
* `IsEulerianCircuit.even_degree` — Every vertex in a graph with an
  Eulerian circuit has even degree
-/


open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
         {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Definition of Eulerian Circuit -/


/-! ## The Degree Parity Theorem -/




open SimpleGraph in
theorem solution    {u : V} {p : G.Walk u u} (hp : p.IsEulerianCircuit) (v : V) :
    Even (G.degree v) := by
  obtain ⟨ hp₁, hp₂ ⟩ := hp;
  have h_deg_even : ∀ v, Even (p.edges.countP (fun e => v ∈ e)) := by
    have h_deg_even : ∀ {u v : V} {p : G.Walk u v}, ∀ w, Even (p.edges.countP (fun e => w ∈ e)) ↔ (w = u ↔ w = v) := by
      intros u v p w; induction' p with u v p ih generalizing w; aesop;
      by_cases hw : w = v <;> by_cases hw' : w = p <;> simp_all +decide;
      · aesop;
      · simp_all +decide [ Nat.even_add_one ];
      · by_cases h : p = ih <;> simp_all +decide [ parity_simps ];
    aesop;
  have h_deg_eq : List.countP (fun e => v ∈ e) p.edges = Finset.card (Finset.filter (fun e => v ∈ e) G.edgeFinset) := by
    rw [ ← hp₂, List.countP_eq_length_filter ];
    rw [ ← Multiset.coe_card ];
    rw [ ← Multiset.toFinset_card_of_nodup ];
    · congr with e ; aesop;
    · exact List.Nodup.filter _ ( hp₁.edges_nodup );
  have h_deg_eq : Finset.card (Finset.filter (fun e => v ∈ e) G.edgeFinset) = Finset.card (G.incidenceFinset v) := by
    grind +suggestions;
  convert h_deg_even v using 1 ; aesop
