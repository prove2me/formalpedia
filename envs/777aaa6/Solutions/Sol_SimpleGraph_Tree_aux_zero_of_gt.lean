-- Prove2me | solution 1 for SimpleGraph.Tree.aux_zero_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:59:36.545833+00:00
-- url     : https://prove2.me/submissions/690b122d-7bf9-40a6-b46b-a7da8a2665bb

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
theorem _root_.solution (n : ℕ) (e : X.edgeSet) (h : n + 1 < X.dist v₀ (X.target v₀ e)) :
    aux w f v₀ n e = 0 := by
  match n with
  | 0 => rfl
  | n + 1 =>
    simp only [aux, dite_eq_left_iff, not_lt]
    intro h
    omega
end SimpleGraph.Tree
