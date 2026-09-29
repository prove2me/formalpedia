-- Prove2me | Definitions.Def_Algebra_AlgebraicTheoryOfAlgebra
-- name    : Algebra_AlgebraicTheoryOfAlgebra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:36:59.58919+00:00
-- url     : https://prove2.me/theorems/1901af46-91c5-4090-bd5a-183bd33f71a1
-- title:
--   Aether Catalog definitions — Algebra_AlgebraicTheoryOfAlgebra
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.AlgebraicTheoryOfAlgebra`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/AlgebraicTheoryOfAlgebra.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Algebra.Foundations.AlgebraicTheoryOfAlgebra

Auto-generated from theorem catalog database.
Domain: Algebra/Foundations
Declarations: 32
-/


/-- An algebraic signature: a type of operation symbols with arities -/
structure AlgSignature where
  /-- The type of operation symbols -/
  OpSym : Type
  /-- The arity of each operation symbol -/
  arity : OpSym → ℕ




/-- A Sig-algebra: a carrier type with interpretations of operation symbols -/
structure SigAlgebra (S : AlgSignature) where
  /-- The carrier set -/
  carrier : Type
  /-- Interpretation of each operation symbol -/
  interp : (f : S.OpSym) → (Fin (S.arity f) → carrier) → carrier

-- ============================================================
-- Section 2: The Lattice of Equational Theories
-- ============================================================




/-- An equational theory over a type is a set of pairs of elements
that are declared equal. Modeled as an equivalence-like relation. -/
structure EquationalTheory (α : Type*) where
  /-- The set of equations, as a relation -/
  eqns : α → α → Prop
  /-- Reflexivity -/
  refl : ∀ a, eqns a a
  /-- Symmetry -/
  symm : ∀ a b, eqns a b → eqns b a
  /-- Transitivity -/
  trans : ∀ a b c, eqns a b → eqns b c → eqns a c




/-- [Section: # CatalogBuild.Algebra.Foundations.AlgebraicTheoryOfAlgebra
Auto-generated from theorem catalog database.
Domain: Algebra/Foundations
Declarations: 32] -/
instance (α : Type*) : LE (EquationalTheory α) where
  le T₁ T₂ := ∀ a b, T₁.eqns a b → T₂.eqns a b




/-- The trivial theory: everything is equal -/
def trivialTheory (α : Type*) : EquationalTheory α where
  eqns := fun _ _ => True
  refl := fun _ => trivial
  symm := fun _ _ _ => trivial
  trans := fun _ _ _ _ _ => trivial




/-- The discrete theory: only reflexive equations -/
def discreteTheory (α : Type*) : EquationalTheory α where
  eqns := fun a b => a = b
  refl := fun _ => rfl
  symm := fun _ _ h => h.symm
  trans := fun _ _ _ h₁ h₂ => h₁.trans h₂




/-- The meet (intersection) of two theories -/
def theoryMeet {α : Type*} (T₁ T₂ : EquationalTheory α) : EquationalTheory α where
  eqns a b := T₁.eqns a b ∧ T₂.eqns a b
  refl a := ⟨T₁.refl a, T₂.refl a⟩
  symm a b h := ⟨T₁.symm a b h.1, T₂.symm a b h.2⟩
  trans a b c h₁ h₂ := ⟨T₁.trans a b c h₁.1 h₂.1, T₂.trans a b c h₁.2 h₂.2⟩













-- ============================================================
-- Section 3: Varieties and the HSP Theorem Structure
-- ============================================================




/-- A variety is a class of algebras closed under H, S, and P. -/
structure Variety (S : AlgSignature) where
  member : SigAlgebra S → Prop




instance (S : AlgSignature) : LE (Variety S) where
  le V₁ V₂ := ∀ A, V₁.member A → V₂.member A












/-- The meet of two varieties = their intersection -/
def varietyMeet (S : AlgSignature) (V₁ V₂ : Variety S) : Variety S where
  member A := V₁.member A ∧ V₂.member A













-- ============================================================
-- Section 4: Free Algebra Construction (Terms)
-- ============================================================




/-- Terms over a signature S with variables from X -/
inductive AlgTerm (S : AlgSignature) (X : Type) : Type where
  | var : X → AlgTerm S X
  | app : (f : S.OpSym) → (Fin (S.arity f) → AlgTerm S X) → AlgTerm S X








/-- Substitution: replace variables in a term -/
def AlgTerm.subst {S : AlgSignature} {X Y : Type}
    (sigma : X → AlgTerm S Y) : AlgTerm S X → AlgTerm S Y
  | .var x => sigma x
  | .app f args => .app f (fun i => (args i).subst sigma)





-- ============================================================
-- Section 5: The Self-Referential Structure
-- ============================================================





















-- ============================================================
-- Section 6: Monad Structure (Algebraic Theory ↔ Monad)
-- ============================================================




/-- The unit of the free algebra monad -/
def freeMonadUnit (S : AlgSignature) (X : Type) : X → AlgTerm S X :=
  AlgTerm.var




/-- The multiplication of the free algebra monad -/
def freeMonadMult (S : AlgSignature) (X : Type) : AlgTerm S (AlgTerm S X) → AlgTerm S X :=
  AlgTerm.subst id









-- ============================================================
-- Section 7: The Grand Self-Reference Theorem
-- ============================================================


