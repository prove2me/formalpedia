-- Prove2me | Definitions.Def_Bridges_PosetTheory_GaloisLatticeZariskiBridge
-- name    : Bridges_PosetTheory_GaloisLatticeZariskiBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:42.060985+00:00
-- url     : https://prove2.me/theorems/d4b8d7cc-9baa-444d-920c-33eef90d7490
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_GaloisLatticeZariskiBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.GaloisLatticeZariskiBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/GaloisLatticeZariskiBridge.lean by skeleton subtraction
import Mathlib
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-! # Galois Connections, Knaster–Tarski, and the Zariski Topology

Note on imports: the four imports above are the foundations requested
(`GaloisConnection`, `CompleteLattice`, `Ideal`, and `PrimeSpectrum`); the
last two module paths are the current Mathlib locations of
`RingTheory.Ideal.Basic` and the prime spectrum basics.  We deliberately do
*not* import any Knaster–Tarski / order fixed-point file: the complete-lattice
structure of Theorem A is built purely from the adjunction axioms together with
the generic order-theoretic builder `completeLatticeOfInf`.

This file bridges Galois connections, order theory and topology with two results.

**Theorem A (Knaster–Tarski for Galois connections).**
Given a Galois connection `l ⊣ u` between complete lattices `α` and `β`, the set of
fixed points of the closure operator `u ∘ l`,
`Fix gc = {x : α // u (l x) = x}`, forms a complete lattice.  The construction is
*from first principles*: we only use the order-theoretic axioms of complete lattices
together with the defining adjunction property of the Galois connection.  In
particular we never invoke any Knaster–Tarski / fixed-point theorem from Mathlib.

The infimum of a family of fixed points is the ambient infimum (the infimum of
closed elements is closed); the supremum is the closure `u (l (⨆ …))` of the
ambient supremum.  The whole complete-lattice structure is then obtained from the
generic builder `completeLatticeOfInf`, which derives every operation purely from
the infimum.

**Theorem B (Zariski topology from a Galois connection).**
For a commutative ring `R`, the pair `l = zeroLocus` (the vanishing set `V(I)`)
and `u = vanishingIdeal` (`S ↦ ⋂ p ∈ S, p.asIdeal`) forms an (antitone) Galois
connection between `Ideal R` and `Set (PrimeSpectrum R)`, and the associated
closure operator `u ∘ l` is exactly the radical of an ideal.
-/

namespace GaloisLatticeZariskiBridge

universe u v

/-! ## Theorem A — Knaster–Tarski for Galois connections -/

section TheoremA

variable {α : Type u} {β : Type v} [CompleteLattice α] [CompleteLattice β]
  {l : α → β} {u : β → α}



/-- The type of fixed points of the closure operator `u ∘ l`. -/
abbrev Fix (_gc : GaloisConnection l u) : Type u := {x : α // u (l x) = x}

namespace Fix

variable (gc : GaloisConnection l u)

/-
**Key lemma.** The infimum of a family of closed elements is again closed:
if every element of `S` is a fixed point of `u ∘ l`, then so is `sInf S`.
-/
lemma closed_sInf (gc : GaloisConnection l u) (S : Set α) (hS : ∀ x ∈ S, u (l x) = x) :
    u (l (sInf S)) = sInf S := by
  refine' le_antisymm _ _;
  · exact le_sInf fun x hx => by simpa [ hS x hx ] using gc.monotone_u ( gc.monotone_l ( sInf_le hx ) ) ;
  · exact gc.le_u_l _

/-- Infimum on the subtype of fixed points: the ambient infimum, which stays closed. -/
instance instInfSet : InfSet (Fix gc) where
  sInf S := ⟨sInf (Subtype.val '' S), by
    apply closed_sInf gc
    rintro x ⟨y, _, rfl⟩
    exact y.2⟩


/-
The ambient infimum is the greatest lower bound inside `Fix gc`.
-/
lemma isGLB_sInf (S : Set (Fix gc)) : IsGLB S (sInf S) := by
  refine' ⟨ fun x hx => _, fun x hx => _ ⟩;
  · exact sInf_le ( Set.mem_image_of_mem _ hx );
  · simp_all +decide [ lowerBounds ];
    exact Subtype.mk_le_mk.mpr ( le_sInf fun y hy => by aesop )

/-- **Theorem A.** The fixed points of the closure operator of a Galois connection
between complete lattices form a complete lattice. -/
noncomputable instance instCompleteLattice : CompleteLattice (Fix gc) :=
  completeLatticeOfInf (Fix gc) (isGLB_sInf gc)

/-
Universal property of the closure operator on `Fix`: for a closed element `x`
and any `a : α`, we have `u (l a) ≤ x ↔ a ≤ x`.  This is the order-theoretic core
that makes `u ∘ l` behave like a closure.
-/

/-
The supremum inside `Fix gc` is the closure `u (l (⨆ …))` of the ambient
supremum, matching the description `supₖ = u (l (⨆ᵢ xᵢ))`.
-/

end Fix

end TheoremA

/-! ## Theorem B — Zariski topology from a Galois connection -/

section TheoremB

open PrimeSpectrum

variable {R : Type u} [CommRing R]






end TheoremB

end GaloisLatticeZariskiBridge


