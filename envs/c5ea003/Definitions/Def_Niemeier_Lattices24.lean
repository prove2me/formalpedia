-- Prove2me | Definitions.Def_Niemeier_Lattices24
-- name    : Niemeier_Lattices24
-- status  : Definition
-- author  : @chlee
-- created : 2026-11-09T09:46:05.920585+00:00
-- url     : https://prove2.me/theorems/0512fc9f-e4b9-45ba-b9aa-22fb58b8d7ae
-- title:
--   Rank-$24$ even unimodular lattices and full integral isometry
-- statement:
--   The definition bundle models lattices on $\mathbb Z^{24}$ by symmetric integer Gram matrices that are positive definite over $\mathbb R$, have even squared norm on every integral vector and determinant $1$. It defines the integral pairing, full integral isometry and its quotient, roots of squared norm $2$, rootlessness and complete-family/classification predicates. The classification is a proposition to prove, with no assumed representative list or completeness certificate.
-- source:
--   J. H. Conway and N. J. A. Sloane, On the enumeration of lattices of determinant one, Journal of Number Theory 15 (1982), 83–94, §2, Table III, §4 Tables V–VI and Theorem 2 (pp.91–93). https://doi.org/10.1016/0022-314X(82)90084-1

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Mathlib-only definitions for the local Niemeier mission proposal.
The Gram matrix records the integral pairing B; squared norm is B(x,x),
not half that value. No classification theorem is assumed here.
-/

set_option autoImplicit false

namespace Niemeier

abbrev Coordinates := Fin 24 → ℤ

/-- A based rank-24 integral lattice. Positive definiteness is over ℝ.
Unimodularity uses determinant +1, appropriate for a positive Gram matrix.
Evenness is required on every integral vector, with squared norm B(x,x). -/
structure EvenUnimodularLattice24 where
  gram : Matrix (Fin 24) (Fin 24) ℤ
  symmetric : gram.IsSymm
  positive : (gram.map (Int.castRingHom ℝ)).PosDef
  even : ∀ x : Coordinates, Even (gram.toBilin' x x)
  unimodular : gram.det = 1

namespace EvenUnimodularLattice24

abbrev pairing (L : EvenUnimodularLattice24) : LinearMap.BilinForm ℤ Coordinates :=
  L.gram.toBilin'

/-- Integral, full isometry, with no orientation or determinant +1 restriction. -/
def Isometric (L K : EvenUnimodularLattice24) : Prop :=
  L.pairing.Equivalent K.pairing

instance isometrySetoid : Setoid EvenUnimodularLattice24 where
  r := Isometric
  iseqv := ⟨fun L => LinearMap.BilinForm.Equivalent.refl L.pairing,
    fun h => LinearMap.BilinForm.Equivalent.symm h,
    fun h h' => LinearMap.BilinForm.Equivalent.trans h h'⟩

/-- Roots are actual integral vectors of squared norm 2. -/
def Roots (L : EvenUnimodularLattice24) :=
  {x : Coordinates // L.pairing x x = 2}

/-- The rootless member of the classification is the Leech isometry class. -/
def Rootless (L : EvenUnimodularLattice24) : Prop :=
  ∀ x : Coordinates, L.pairing x x ≠ 2



end EvenUnimodularLattice24

/-- The quotient forgets the chosen integral basis. -/
abbrev IsometryClass := Quotient EvenUnimodularLattice24.isometrySetoid

/-- A complete family of 24 pairwise nonisometric lattices. -/
def CompleteFamily (C : Fin 24 → EvenUnimodularLattice24) : Prop :=
  (∀ i j, (C i).Isometric (C j) ↔ i = j) ∧
  ∀ L : EvenUnimodularLattice24, ∃! i : Fin 24, L.Isometric (C i)

/-- Main target: 24 classes, with index 0 the unique rootless class.
The other 23 classes have roots. This is a proposition to prove, not a certificate
field supplied as an assumption about candidates. Concrete named Gram models
and identification with the classical root-system table are further obligations. -/
def ClassificationStatement : Prop :=
  ∃ C : Fin 24 → EvenUnimodularLattice24,
    CompleteFamily C ∧ ∀ i : Fin 24, (C i).Rootless ↔ i = 0





end Niemeier


