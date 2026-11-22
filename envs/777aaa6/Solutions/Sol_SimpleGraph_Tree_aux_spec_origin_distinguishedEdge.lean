-- Prove2me | solution 1 for SimpleGraph.Tree.aux_spec_origin_distinguishedEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:59:58.305838+00:00
-- url     : https://prove2.me/submissions/3fc6a66f-debd-479b-8a60-934140db2fca

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
theorem _root_.solution (hnonempty : (X.outwardEdgeCone v₀ v₀).Nonempty) :
    aux w f v₀ 1 (distinguishedEdge v₀ v₀ hnonempty) = (w v₀)⁻¹ • f v₀ := by
  have : X.dist v₀ v₀ = 0 := by simp
  simp [aux, norm_target_eq_norm_source_add_one, this, auxBorder]
end SimpleGraph.Tree
