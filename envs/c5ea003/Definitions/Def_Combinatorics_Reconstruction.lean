-- Prove2me | Definitions.Def_Combinatorics_Reconstruction
-- name    : Combinatorics_Reconstruction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:48:42.889107+00:00
-- url     : https://prove2.me/theorems/4f976620-6fd2-4a60-9553-e695ceee54cd
-- title:
--   Aether Catalog definitions — Combinatorics_Reconstruction
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.Reconstruction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/Reconstruction.lean by skeleton subtraction
import Mathlib

/-!
# Vertex-deleted decks and Kelly's counting lemma

The full reconstruction conjecture is open.  This file develops its standard
finite-graph language, proves the double-counting core of Kelly's lemma, and
proves reconstruction for the two extremal graph classes: edgeless and complete
graphs.
-/

namespace Catalog.Combinatorics.Reconstruction

open Finset SimpleGraph
open scoped Sym2

variable {V W U : Type*}

/-- The card obtained by deleting one vertex and taking the induced graph. -/
abbrev vertexCard (G : SimpleGraph V) (v : V) : SimpleGraph {x : V // x ≠ v} :=
  G.induce ({v}ᶜ : Set V)

/-- Two finite graphs have the same deck when their vertices can be paired so
that corresponding vertex-deleted cards are isomorphic. -/
def SameDeck (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ e : V ≃ W, ∀ v : V, Nonempty (vertexCard G v ≃g vertexCard H (e v))

/-- A family of `k`-element vertex sets, used for the abstract form of Kelly's
counting argument. -/
def UniformFamily [Fintype V] [DecidableEq V] (A : Finset (Finset V)) (k : ℕ) : Prop :=
  ∀ s ∈ A, s.card = k

/-- The members of a family which survive deletion of `v`. -/
def survivingSets [DecidableEq V] (A : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  A.filter fun s => v ∉ s


/-- The family of vertex sets inducing a copy of the finite pattern `F`. -/
noncomputable def inducedCopyFamily [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph U) [Fintype U] : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun s =>
    s.card = Fintype.card U ∧ Nonempty (G.induce (s : Set V) ≃g F)








end Catalog.Combinatorics.Reconstruction

/-!
# Complement compatibility for vertex decks

Taking graph complements preserves and reflects equality of vertex-deleted decks.
-/

namespace Catalog.Combinatorics.Reconstruction

open SimpleGraph

variable {V W : Type*}

/-- A graph isomorphism induces an isomorphism of the complementary graphs. -/
def isoCompl {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) : Gᶜ ≃g Hᶜ :=
  { f.toEquiv with
    map_rel_iff' := by
      intro v w
      simp [f.map_adj_iff] }




end Catalog.Combinatorics.Reconstruction


