-- Prove2me | solution 1 for SimpleGraph.Tree.aux_spec_distinguishedEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:00:49.218825+00:00
-- url     : https://prove2.me/submissions/51487035-1aaa-444f-bf1d-bd59fb76295a

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Harmonic_Basic
import Theorems.Thm_SimpleGraph_Tree_aux_extends

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
theorem _root_.solution (n : ℕ) (v : V) (hv : X.dist v₀ v + 1 = n) (hlt : 0 < X.dist v₀ v)
    (hnonempty : (X.outwardEdgeCone v₀ v).Nonempty) :
    aux w f v₀ n (X.distinguishedEdge v₀ v hnonempty) =
      (w v)⁻¹ • f v - aux w f v₀ n (X.edgeTowardsOrigin v₀ v hlt) := by
  match n with
  | 0 => simp at hv
  | 1 =>
    /- Then `v = v₀`, but this is excluded. -/
    simp only [add_eq_right] at hv
    simp [hv] at hlt
  | n + 2 =>
      conv_lhs => rw [aux]
      simp only
      split_ifs
      · next h =>
        /- causes contradiction since `X.dist v₀ v + 1 = n + 1` -/
        rw [← hv] at h
        have : X.dist v₀ (source v₀ (distinguishedEdge v₀ v hnonempty)) + 1 <
            X.dist v₀ (target v₀ (distinguishedEdge v₀ v hnonempty)) := by
          simpa
        rw [norm_target_eq_norm_source_add_one] at this
        omega
      · next h₁ h₂ =>
        rw [aux]
        rw [add_left_inj, ← source_distinguishedEdge v₀ v hnonempty] at hv
        rw [← hv] at h₂
        have := norm_source_lt_norm_target v₀ (distinguishedEdge v₀ v hnonempty)
        omega
      · rw [auxBorder]
        simp only [source_distinguishedEdge, ↓reduceIte, sub_right_inj]
        rw [← aux_extends]
        simp only [edgeTowardsOrigin_target_eq]
        rw [add_left_inj] at hv
        rw [hv]
end SimpleGraph.Tree
