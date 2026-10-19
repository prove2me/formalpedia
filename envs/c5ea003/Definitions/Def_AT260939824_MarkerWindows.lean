-- Prove2me | Definitions.Def_AT260939824_MarkerWindows
-- name    : AT260939824_MarkerWindows
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:42:01.274199+00:00
-- url     : https://prove2.me/theorems/bfe7f2bd-34c3-411d-8cf5-2e3b725d94e9
-- title:
--   Finite separated marker-window patterns
-- statement:
--   For natural numbers $d,L$, a marker window is a finite box of lattice displacements in $\mathbb Z^d$. Its allowed patterns are finite subsets satisfying the specified separation and covering conditions. The resulting marker-pattern type is finite and is equipped with its discrete topology. These are the literal finite window objects used in the paper, with the original window and distance conventions.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/MarkerWindows.lean, selected declaration lines 22-23, 29-30, 32-34, 36-39, 45-54, 56, 58-59; SHA-256 edf194ff4bb9dad1f990790bf4466d2c2e6c8bcf0a8181b4d4191e1eb1889b9a. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite

set_option autoImplicit false

/-!
# Finite separated marker windows

The finite target in Lemma 7.3 of arXiv:2609.39824v1. Its adjacency is
exactly the overlap relation (9), and looplessness is proved from marker
separation and coverage, rather than imposed in the definition.
-/

namespace AbelianTargets

noncomputable section

def markerBox (d L : ℕ) : Finset (Lattice d) :=
  Fintype.piFinset fun _ => Finset.Icc (-(2 * (L : ℤ))) (2 * (L : ℤ))



def MarkerSeparated {d : ℕ} (L : ℕ) (D : Finset (Lattice d)) : Prop :=
  ∀ a ∈ D, ∀ b ∈ D, a ≠ b → ∃ i, (L : ℤ) < |a i - b i|

def MarkerCovering {d : ℕ} (L : ℕ) (D : Finset (Lattice d)) : Prop :=
  ∀ u : Lattice d, (∀ i, |u i| ≤ (L : ℤ)) →
    ∃ a ∈ D, ∀ i, |u i - a i| ≤ (L : ℤ)

/-- The exact finite vertex set in Lemma 7.3. -/
def MarkerPattern (d L : ℕ) :=
  {D : Finset (Lattice d) //
    D ⊆ markerBox d L ∧ MarkerSeparated L D ∧ MarkerCovering L D}

namespace MarkerPattern

variable {d L : ℕ}

instance : Finite (MarkerPattern d L) := by
  classical
  apply Finite.of_injective
    (fun D : MarkerPattern d L =>
      (⟨D.val, Finset.mem_powerset.mpr D.property.1⟩ :
        {s : Finset (Lattice d) // s ∈ (markerBox d L).powerset}))
  intro D E h
  apply Subtype.ext
  exact congrArg
    (fun t : {s : Finset (Lattice d) // s ∈ (markerBox d L).powerset} => t.val) h

noncomputable instance : Fintype (MarkerPattern d L) := Fintype.ofFinite _

instance : TopologicalSpace (MarkerPattern d L) := ⊥
instance : DiscreteTopology (MarkerPattern d L) := ⟨rfl⟩











end MarkerPattern



namespace SignedUnit

variable {d : ℕ} {g : Lattice d}







end SignedUnit







































end

end AbelianTargets


