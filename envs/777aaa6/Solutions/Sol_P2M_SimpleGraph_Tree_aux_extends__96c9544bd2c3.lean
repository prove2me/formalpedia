-- Prove2me | solution 1 for P2M_SimpleGraph_Tree_aux_extends__96c9544bd2c3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:59:41.74635+00:00
-- url     : https://prove2.me/submissions/212c0af8-0ad2-4675-ab71-12a1985f010a

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Harmonic_Basic

set_option autoImplicit false
suppress_compilation
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable {V : Type*} [DecidableEq V]
open BigOperators
open SimpleGraph
open SimpleGraph.Tree
variable {X : SimpleGraph.Tree V} [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ) (f : V → M)
variable (v₀ : V)
variable (n : ℕ) (g : X.edgeSet → M)
namespace SimpleGraph.Tree
theorem _root_.solution (n : ℕ) (e : X.edgeSet) (he : X.dist v₀ (X.target v₀ e) ≤ n) :
    aux w f v₀ (X.dist v₀ (X.target v₀ e)) e = aux w f v₀ n e := by
  match n with
  | 0 =>
    have : (X.dist v₀ (target v₀ e)) = 0 := by omega
    simp only [aux, this]
  | n + 1 =>
    simp only [aux]
    split_ifs
    · next h => omega
    · next h => apply solution n e h
    · next h₁ h₂ =>
      have : X.dist v₀ (target v₀ e) = n + 1 := by omega
      simp_rw [this]
      simp only [aux]
      split_ifs
      · rfl
end SimpleGraph.Tree
