-- Prove2me | Definitions.Def_AT260939824_MarkerPriorities
-- name    : AT260939824_MarkerPriorities
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:44:49.24346+00:00
-- url     : https://prove2.me/theorems/2f512532-517c-4139-b730-73f6a8846293
-- title:
--   Finite marker-proximity neighborhoods
-- statement:
--   Let a free lattice action on $X$ have anisotropic clopen markers with scales $L_i$. For a natural radius multiplier $S$, the scaled neighborhood of a marker consists of lattice displacements bounded coordinatewise by $SL_i$ that reach another marker. These displacements give a finite neighbor list and a simple marker-proximity graph. Anisotropic packing bounds its size by $(2S+1)^d$ when all scales are positive.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/MarkerPriorities.lean, selected declaration lines 20-24, 26-31, 42-50, 52-57, 70-72; SHA-256 eea138a37e4856c5f0023b7a1cde74f87d32c4055a60d716211686d01cc78b31. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasPacking
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite

set_option autoImplicit false

/-!
# Continuous marker priorities with a scale-independent color bound

The marker proximity graph is the actual induced finite-displacement
graph. Its finite neighbors are counted by the anisotropic packing bound.
The general continuous finite-coloring theorem supplies the priorities.
-/

namespace AbelianTargets

noncomputable section

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X]

def scaledMarkerNeighborhood (M : AnisotropicClopenMarkers d L X) (S : ℕ)
    (x : M.markers) : Finset (Lattice d) := by
  classical
  exact (Fintype.piFinset (fun i => Finset.Icc (-(S : ℤ)*(L i : ℤ)) ((S : ℤ)*(L i : ℤ)))).filter
    (fun g => g +ᵥ x.val ∈ M.markers)

@[simp] theorem mem_scaledMarkerNeighborhood (M : AnisotropicClopenMarkers d L X)
    (S : ℕ) (x : M.markers) (g : Lattice d) :
    g ∈ scaledMarkerNeighborhood M S x ↔
      (∀ i,-(S : ℤ)*(L i : ℤ) ≤ g i ∧ g i ≤ (S : ℤ)*(L i : ℤ)) ∧
        g +ᵥ x.val ∈ M.markers := by
  simp only [scaledMarkerNeighborhood,Finset.mem_filter,Fintype.mem_piFinset,Finset.mem_Icc]



theorem scaledMarkerNeighborhood_card_le (M : AnisotropicClopenMarkers d L X)
    (hL : ∀ i,1 ≤ L i) (S : ℕ) (x : M.markers) :
    (scaledMarkerNeighborhood M S x).card ≤ (2*S+1)^d := by
  apply anisotropic_marker_packing S L hL
  · intro g hg
    exact ((mem_scaledMarkerNeighborhood M S x g).mp hg).1
  · intro g hg h hh hne
    exact M.separated x.val g h ((mem_scaledMarkerNeighborhood M S x g).mp hg).2
      ((mem_scaledMarkerNeighborhood M S x h).mp hh).2 hne

def markerNeighborList (M : AnisotropicClopenMarkers d L X) (S : ℕ)
    (x : M.markers) : Finset M.markers := by
  classical
  exact ((scaledMarkerNeighborhood M S x).erase 0).attach.image (fun g =>
    ⟨g.val +ᵥ x.val,((mem_scaledMarkerNeighborhood M S x g.val).mp
      (Finset.mem_of_mem_erase g.property)).2⟩)



def markerProximityGraph (M : AnisotropicClopenMarkers d L X) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X)) : SimpleGraph M.markers :=
  (anisotropicDisplacementGraph (fun i => S*L i) free).induce M.markers



variable [ContinuousVAdd (Lattice d) X] [T1Space X] [SecondCountableTopology X]





end

end AbelianTargets


