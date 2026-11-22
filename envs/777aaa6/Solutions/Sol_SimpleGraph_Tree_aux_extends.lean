-- Prove2me | solution 1 for SimpleGraph.Tree.aux_extends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:00:12.112655+00:00
-- url     : https://prove2.me/submissions/c8cfcfbd-e779-4e40-ba80-3ba299963ae0

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Harmonic_Basic
import Theorems.Thm_SimpleGraph_Tree_aux_zero_of_gt

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
    aux w f v₀ (n + 1) e = aux w f v₀ n e := by
  simp_rw [aux]
  split_ifs
  · rwa [aux_zero_of_gt]
  · rfl
end SimpleGraph.Tree
