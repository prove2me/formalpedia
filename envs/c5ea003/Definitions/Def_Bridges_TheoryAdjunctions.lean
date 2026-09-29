-- Prove2me | Definitions.Def_Bridges_TheoryAdjunctions
-- name    : Bridges_TheoryAdjunctions
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:48.231965+00:00
-- url     : https://prove2.me/theorems/8be6f369-44ab-4c70-ac4f-01fb4bff05a4
-- title:
--   Aether Catalog definitions — Bridges_TheoryAdjunctions
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TheoryAdjunctions`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TheoryAdjunctions.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_TheoryMorphisms
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Theory Adjunctions: Optimal Cross-Domain Translation via Galois Connections

An adjunction `F ⊣ G` between research theories formalizes the idea that
`F` is the *best possible monotone encoding* and `G` reconstructs the
*strongest compatible approximation*.

## Main Results

* `TheoryAdjunction` — Adjunction as Galois connection on invariant preorders.
* `TheoryAdjunction.comp` — Adjunctions compose.
* `TheoryAdjunction.unit` / `counit` — Unit/counit inequalities.
* `TheoryAdjunction.transport_lower_bound` — Lower bounds survive round-trips.
* `TheoryAdjunction.sharp_lower_bound_fwd` — Lower bounds witnessed by the adjunction.
* `not_heightToCell_adjunction_exists` — Impossibility for Height ⊣ Cell.
* `proj_sect_adjunction` — Nontrivial concrete adjunction (projection ⊣ section).
* `composed_pair_triple_adjunction` — Composition across three theories.
* `TheoryAdjunction.round_trip_idempotent` — Round-trip stabilizes in one pass.
* `TheoryAdjunction.right_adjoint_inv_unique` — Right adjoints unique up to Inv.
-/


/-! ## §1. The Invariant Preorder -/

/-- The **invariant preorder**: `x ≤_T y` iff `T.Inv x ≤ T.Inv y`. -/
def theoryLE (T : ResearchTheory) (x y : T.Carrier) : Prop :=
  T.Inv x ≤ T.Inv y




/-! ## §2. Theory Adjunction: Definition -/

/-- A **theory adjunction** `F ⊣ G` is a Galois connection between the
    invariant preorders:
    `U.Inv (F x) ≤ U.Inv y ⟺ T.Inv x ≤ T.Inv (G y)`. -/
structure TheoryAdjunction {T U : ResearchTheory}
    (F : TheoryHom T U) (G : TheoryHom U T) : Prop where
  gc : ∀ x y, theoryLE U (F.toFun x) y ↔ theoryLE T x (G.toFun y)

/-! ## §3. Unit and Counit Inequalities -/





/-! ## §4. Composition of Adjunctions -/


/-! ## §5. Invariant Transfer Theorems -/



/-! ## §6. Sharp Lower-Bound Characterization -/




/-! ## §7. Identity Adjunction -/


/-! ## §8. Monotonicity from Adjunction -/




/-! ## §9. Construct from biconditional -/



/-! ## §10. Nontrivial Adjunction: Projection ⊣ Section -/

/-- Source theory: pairs `(a, b)` with invariant = first component. -/
def PairTheory : ResearchTheory where
  Carrier := ℕ × ℕ
  Inv := fun p => p.1

/-- Target theory: `ℕ` with identity invariant. -/
def NatIdTheory : ResearchTheory where
  Carrier := ℕ
  Inv := _root_.id

/-- Left adjoint: projection onto first component. -/
def projMorphism : TheoryHom PairTheory NatIdTheory where
  toFun := fun p => p.1
  monotone_inv := fun _ => le_refl _

/-- Right adjoint: section `n ↦ (n, 0)`. -/
def sectMorphism : TheoryHom NatIdTheory PairTheory where
  toFun := fun n => (n, 0)
  monotone_inv := fun _ => le_refl _


/-! ## §11. Impossibility Theorem: Height-Cell Adjunction -/


/-! ## §12. Composition Example -/

/-- Triple theory: `ℕ × ℕ × ℕ` with invariant = first component. -/
def TripleTheory : ResearchTheory where
  Carrier := ℕ × ℕ × ℕ
  Inv := fun p => p.1

/-- Embedding into triple theory. -/
def natToTriple : TheoryHom NatIdTheory TripleTheory where
  toFun := fun n => (n, 0, 0)
  monotone_inv := fun _ => le_refl _

/-- Projection from triple theory. -/
def tripleToNat : TheoryHom TripleTheory NatIdTheory where
  toFun := fun p => p.1
  monotone_inv := fun _ => le_refl _




/-! ## §13. Adjunction Uniqueness -/


