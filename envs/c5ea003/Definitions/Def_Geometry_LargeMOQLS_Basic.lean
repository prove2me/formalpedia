-- Prove2me | Definitions.Def_Geometry_LargeMOQLS_Basic
-- name    : Geometry_LargeMOQLS_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:50.73475+00:00
-- url     : https://prove2.me/theorems/9c62d9f9-24f2-4236-bc35-ea701e99f7b2
-- title:
--   Aether Catalog definitions — Geometry_LargeMOQLS_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.LargeMOQLS.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/LargeMOQLS/Basic.lean by skeleton subtraction
import Mathlib

open scoped BigOperators ComplexConjugate

namespace LargeMOQLS

/-- The standard coordinate vector indexed by `ι`. -/
def basisVector {ι : Type*} [DecidableEq ι] (i : ι) : ι → ℂ :=
  fun j => if j = i then 1 else 0

/-- An array of vectors is a quantum Latin square when every row and every column
is an orthonormal basis. -/
structure QuantumLatinSquare (ι : Type*) [Fintype ι] [DecidableEq ι] where
  entry : ι → ι → (ι → ℂ)
  row_orthonormal : ∀ i j k,
    (∑ x, conj (entry i j x) * entry i k x) = if j = k then 1 else 0
  column_orthonormal : ∀ i j k,
    (∑ x, conj (entry j i x) * entry k i x) = if j = k then 1 else 0

/-- Two quantum Latin squares are orthogonal when the entrywise tensor products
form an orthonormal basis of the tensor-square coordinate space. -/
def QuantumOrthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : QuantumLatinSquare ι) : Prop :=
  ∀ i j k l,
    (∑ p : ι × ι,
      conj (A.entry i j p.1 * B.entry i j p.2) *
        (A.entry k l p.1 * B.entry k l p.2)) =
      if i = k ∧ j = l then 1 else 0

/-- Replace each symbol in a classical array by its standard basis vector. -/
def basisArray {ι : Type*} [DecidableEq ι] (L : ι → ι → ι) :
    ι → ι → (ι → ℂ) :=
  fun i j => basisVector (L i j)


/-
Any classical Latin square gives a quantum Latin square in the computational basis.
-/
def classicalToQuantum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ι → ι → ι)
    (hrow : ∀ i, Function.Injective (L i))
    (hcol : ∀ j, Function.Injective (fun i => L i j)) : QuantumLatinSquare ι where
  entry := basisArray L
  row_orthonormal := by
    unfold basisArray;
    simp +decide [ basisVector ];
    grind
  column_orthonormal := by
    intro i j k; rw [ Finset.sum_eq_single ( L j i ) ] <;> simp +decide [ basisArray, basisVector ] ;
    · simp +decide [ hcol i |> Function.Injective.eq_iff ];
    · tauto

/-
Orthogonal classical arrays induce orthogonal quantum Latin squares.
-/

section Affine

variable {K : Type*} [Fintype K] [DecidableEq K] [Field K]

/-- The affine square of slope `a`: its `(x,y)` entry is `a*x+y`. -/
def affineSquare (a : K) : K → K → K := fun x y => a * x + y

omit [Fintype K] [DecidableEq K] in
lemma affineSquare_row_injective (a x : K) :
    Function.Injective (affineSquare a x) := by
  exact fun b c h => by unfold affineSquare at h; simpa using h;

omit [Fintype K] [DecidableEq K] in
lemma affineSquare_column_injective {a : K} (ha : a ≠ 0) (y : K) :
    Function.Injective (fun x => affineSquare a x y) := by
  exact fun x x' h => mul_left_cancel₀ ha <| by unfold affineSquare at h; linear_combination' h;

/-- Every nonzero slope produces an affine quantum Latin square. -/
def affineQuantumLatinSquare (a : K) (ha : a ≠ 0) : QuantumLatinSquare K :=
  classicalToQuantum (affineSquare a) (affineSquare_row_injective a)
    (affineSquare_column_injective ha)


/-
Distinct nonzero affine slopes give orthogonal quantum Latin squares.
-/

/-
The nonzero elements of a finite field index a mutually orthogonal family
of quantum Latin squares.
-/

/-
The affine construction contains exactly `|K|-1` squares.
-/

end Affine




end LargeMOQLS


