-- Prove2me | Definitions.Def_Geometry_NonDesarguesianWorlds
-- name    : Geometry_NonDesarguesianWorlds
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:45:18.206153+00:00
-- url     : https://prove2.me/theorems/db8fe5c9-8ed7-44e4-9803-797748c6ae6a
-- title:
--   Aether Catalog definitions — Geometry_NonDesarguesianWorlds
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.NonDesarguesianWorlds`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/NonDesarguesianWorlds.lean by skeleton subtraction
import Mathlib

/-!
# Projective completion of a planar ternary ring

This file isolates the incidence-theoretic core of coordinatization.  Multiplication
need not be associative: the three solution axioms of a planar ternary operation
are exactly what the usual affine-coordinate proof needs in order to construct a
projective plane.
-/

namespace NonDesarguesianWorlds

/-- The solution axioms needed from a planar ternary operation.  The pair in
`two_points` is `(slope, intercept)`; the pair in `two_slopes` is `(x,y)`.
No associativity or distributivity is assumed. -/
structure PlanarTernaryRing (α : Type*) where
  ternary : α → α → α → α
  intercept : ∀ x m y, ∃! b, ternary x m b = y
  two_points : ∀ {x₁ x₂ : α}, x₁ ≠ x₂ → ∀ y₁ y₂,
    ∃! mb : α × α,
      ternary x₁ mb.1 mb.2 = y₁ ∧ ternary x₂ mb.1 mb.2 = y₂
  two_slopes : ∀ {m₁ m₂ : α}, m₁ ≠ m₂ → ∀ b₁ b₂,
    ∃! xy : α × α,
      xy.2 = ternary xy.1 m₁ b₁ ∧ xy.2 = ternary xy.1 m₂ b₂

/-- Points in the projective completion: affine points, one point for each
slope, and the distinguished point of the vertical direction. -/
inductive Point (α : Type*)
  | affine : α → α → Point α
  | ideal : α → Point α
  | verticalIdeal : Point α
  deriving DecidableEq, Fintype

/-- Lines in the projective completion: ordinary affine lines, vertical lines,
and the line at infinity. -/
inductive Line (α : Type*)
  | ordinary : α → α → Line α
  | vertical : α → Line α
  | atInfinity : Line α
  deriving DecidableEq, Fintype

/-- Incidence in the completion of a planar ternary ring. -/
def Incident {α : Type*} (R : PlanarTernaryRing α) : Point α → Line α → Prop
  | .affine x y, .ordinary m b => y = R.ternary x m b
  | .affine x _, .vertical a => x = a
  | .affine _ _, .atInfinity => False
  | .ideal m, .ordinary n _ => m = n
  | .ideal _, .vertical _ => False
  | .ideal _, .atInfinity => True
  | .verticalIdeal, .ordinary _ _ => False
  | .verticalIdeal, .vertical _ => True
  | .verticalIdeal, .atInfinity => True



/-- The two characteristic unique-incidence axioms of a projective plane. -/
def HasProjectiveIncidence {P L : Type*} (I : P → L → Prop) : Prop :=
  (∀ ⦃p q⦄, p ≠ q → ∃! l, I p l ∧ I q l) ∧
  (∀ ⦃l k⦄, l ≠ k → ∃! p, I p l ∧ I p k)


/-- The constructors of `Point` exhibit it as a disjoint sum. -/
def pointEquiv (α : Type*) : Point α ≃ (α × α) ⊕ α ⊕ Unit where
  toFun
    | .affine x y => .inl (x, y)
    | .ideal m => .inr (.inl m)
    | .verticalIdeal => .inr (.inr ())
  invFun
    | .inl (x, y) => .affine x y
    | .inr (.inl m) => .ideal m
    | .inr (.inr _) => .verticalIdeal
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with xy | rest
    · rfl
    · rcases rest with m | u
      · rfl
      · cases u
        rfl

/-- The constructors of `Line` exhibit it as the same disjoint sum. -/
def lineEquiv (α : Type*) : Line α ≃ (α × α) ⊕ α ⊕ Unit where
  toFun
    | .ordinary m b => .inl (m, b)
    | .vertical a => .inr (.inl a)
    | .atInfinity => .inr (.inr ())
  invFun
    | .inl (m, b) => .ordinary m b
    | .inr (.inl a) => .vertical a
    | .inr (.inr _) => .atInfinity
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with mb | rest
    · rfl
    · rcases rest with a | u
      · rfl
      · cases u
        rfl



/-- Associativity is equivalent to every element belonging to the left nucleus.
This is the precise algebraic obstruction used in quasifield coordinatizations. -/
def LeftNucleus {Q : Type*} (mul : Q → Q → Q) : Set Q :=
  {a | ∀ b c, mul a (mul b c) = mul (mul a b) c}



end NonDesarguesianWorlds


