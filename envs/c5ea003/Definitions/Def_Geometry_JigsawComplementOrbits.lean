-- Prove2me | Definitions.Def_Geometry_JigsawComplementOrbits
-- name    : Geometry_JigsawComplementOrbits
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:26:28.257382+00:00
-- url     : https://prove2.me/theorems/7f7bf63f-8912-4530-868f-50d26b6c5f19
-- title:
--   Aether Catalog definitions — Geometry_JigsawComplementOrbits
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.JigsawComplementOrbits`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/JigsawComplementOrbits.lean by skeleton subtraction
import Mathlib

/-!
# Free complementation orbits for jigsaw solution spaces

A global tab--blank complement transports assemblies of a framed puzzle to
assemblies of the complemented puzzle.  The correct combined solution space is
a *tagged* disjoint union.  This file proves a stronger form of the proposed
parity conjecture: no hypothesis excluding self-dual puzzles is required.

The result is deliberately independent of a particular geometric encoding.  Its
only geometric input is the equivalence of complete assembly spaces induced by
complementing every non-flat edge.  All orbit and counting consequences then
follow formally and without quotienting interchangeable pieces.
-/

namespace JigsawComplementOrbits

section TaggedComplement

variable {α β : Type*}

/-- The involution on a tagged pair of spaces induced by an equivalence between
its two sides. -/
def taggedComplement (e : α ≃ β) : α ⊕ β → α ⊕ β
  | Sum.inl a => Sum.inr (e a)
  | Sum.inr b => Sum.inl (e.symm b)







end TaggedComplement

/-! ## Abstract framed-puzzle consequence -/

/-- Data common to geometric complement constructions: a type of framed
puzzles, a finite assembly space for each puzzle, global edge complementation,
and the induced bijection of complete assemblies. -/
structure FramedComplementSystem where
  Puzzle : Type*
  Assembly : Puzzle → Type*
  complement : Puzzle → Puzzle
  complement_involutive : Function.Involutive complement
  assemblyComplement : (p : Puzzle) → Assembly p ≃ Assembly (complement p)
  finiteAssembly : (p : Puzzle) → Fintype (Assembly p)

namespace FramedComplementSystem

/-- Original and complemented assemblies, with a tag recording the frame in
which the assembly lives. -/
abbrev CombinedAssemblies (S : FramedComplementSystem) (p : S.Puzzle) :=
  S.Assembly p ⊕ S.Assembly (S.complement p)

/-- Global tab--blank complementation on the combined assembly space. -/
def complementAssembly (S : FramedComplementSystem) (p : S.Puzzle) :
    S.CombinedAssemblies p → S.CombinedAssemblies p :=
  taggedComplement (S.assemblyComplement p)




end FramedComplementSystem

/-! ## Sharpness experiment: a self-dual puzzle

The one-puzzle system below is globally self-dual and has one assembly.  Its
tagged combined space nevertheless has two elements and the complement action
swaps them.  Thus non-self-duality is not necessary for freeness on the tagged
union. -/

/-- A minimal self-dual framed system with one puzzle and one assembly. -/
def selfDualSingletonSystem : FramedComplementSystem where
  Puzzle := Unit
  Assembly := fun _ => Unit
  complement := id
  complement_involutive := by intro p; rfl
  assemblyComplement := fun _ => Equiv.refl Unit
  finiteAssembly := fun _ => inferInstance

instance selfDualSingletonAssemblyFintype (p : selfDualSingletonSystem.Puzzle) :
    Fintype (selfDualSingletonSystem.Assembly p) :=
  selfDualSingletonSystem.finiteAssembly p



end JigsawComplementOrbits


