-- Prove2me | Definitions.Def_Bridges_FourierAsFunctor
-- name    : Bridges_FourierAsFunctor
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:20:37.918097+00:00
-- url     : https://prove2.me/theorems/e0262e26-6a21-498f-9a3a-dcb317ef447d
-- title:
--   Aether Catalog definitions — Bridges_FourierAsFunctor
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.FourierAsFunctor`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/FourierAsFunctor.lean by skeleton subtraction
import Mathlib

/-!
# Fourier analysis as a functor: a finite-dimensional categorical model

This file isolates a rigorous algebraic core of the proposed bridge. Objects are coordinate
spaces `K^(Fin n)` and morphisms are matrices. Transposition realizes the contravariant
character-dual functor and gives an equivalence with the opposite category. A Fourier matrix
is an isomorphism, but the bold claim that Fourier matrices form a natural endomorphism for
*all* linear maps is false; an explicit two-dimensional counterexample is proved below.
-/

open CategoryTheory Matrix

universe u

namespace FourierAsFunctor

/-- A skeleton of finite free `K`-modules: object `n` represents `K^(Fin n)` and a
morphism `m ⟶ n` is an `n × m` matrix. -/
abbrev FinFreeMat (_K : Type u) := ℕ

namespace FinFreeMat

variable (K : Type u) [CommRing K]

instance : Category (FinFreeMat K) where
  Hom m n := Matrix (Fin n) (Fin m) K
  id n := 1
  comp A B := B * A
  assoc := by intros; exact (Matrix.mul_assoc _ _ _).symm
  id_comp := by intros; apply Matrix.mul_one
  comp_id := by intros; apply Matrix.one_mul


/-- Character duality on finite coordinate modules. On arrows it is matrix transposition,
so its variance is reversed exactly as in `Hom(-, K)`. -/
def dualFunctor : (FinFreeMat K)ᵒᵖ ⥤ FinFreeMat K where
  obj X := X.unop
  map f := f.unop.transpose
  map_id X := Matrix.transpose_one
  map_comp f g := by
    apply Matrix.ext; intro i j
    change (∑ k, f.unop j k * g.unop k i) = ∑ k, g.unop k i * f.unop j k
    exact Finset.sum_congr rfl (fun k _ => mul_comm (f.unop j k) (g.unop k i))






/-- The unnormalized discrete Fourier matrix. -/
def fourierMatrix (ω : K) (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  fun j i => ω ^ (i.val * j.val)

end FinFreeMat

section ActualPontryaginDual

variable {A B C : Type*}
  [CommGroup A] [CommGroup B] [CommGroup C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]


end ActualPontryaginDual

section RationalCounterexample

/-- The two-point Fourier matrix over `ℚ`. -/
def dftTwo : Matrix (Fin 2) (Fin 2) ℚ := FinFreeMat.fourierMatrix ℚ (-1) 2

/-- Its explicitly normalized inverse. -/
def idftTwo : Matrix (Fin 2) (Fin 2) ℚ := fun i j => (1 / 2) * dftTwo i j




/-- Projection onto the first coordinate. -/
def firstProjection : Matrix (Fin 2) (Fin 2) ℚ :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0


/-- Coordinate support size, used for a precise test of a purported categorical
uncertainty principle. -/
def supportSize {n : ℕ} (v : Fin n → ℚ) : ℕ := Finset.univ.filter (v · ≠ 0) |>.card

/-- The first basis vector in dimension two. -/
def deltaZero : Fin 2 → ℚ := fun i => if i = 0 then 1 else 0


end RationalCounterexample

end FourierAsFunctor


