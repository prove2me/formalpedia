-- Prove2me | Definitions.Def_EML_SPBExtended_LatticeTreeCorrespondence
-- name    : EML_SPBExtended_LatticeTreeCorrespondence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:57.690481+00:00
-- url     : https://prove2.me/theorems/5ce47b0f-ef49-4b59-b14f-3b01bb7fbabc
-- title:
--   Aether Catalog definitions — EML_SPBExtended_LatticeTreeCorrespondence
-- statement:
--   Definition bundle for the Aether Catalog module `EML.SPBExtended.LatticeTreeCorrespondence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/SPBExtended/LatticeTreeCorrespondence.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Pythagorean.TreeFactoring.LatticeTreeCorrespondence

Auto-generated from theorem catalog database.
Domain: Pythagorean/TreeFactoring
Declarations: 48
-/

/-- Berggren 2×2 matrix M₁ ∈ SL(2,ℤ) -/
def berggren_M₁' : Matrix (Fin 2) (Fin 2) ℤ := !![2, -1; 1, 0]

/-- Berggren 2×2 matrix M₃ ∈ SL(2,ℤ) -/
def berggren_M₃' : Matrix (Fin 2) (Fin 2) ℤ := !![1, 2; 0, 1]

/-- M₁ inverse -/
def berggren_M₁_inv' : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 2]

/-- M₃ inverse -/
def berggren_M₃_inv' : Matrix (Fin 2) (Fin 2) ℤ := !![1, -2; 0, 1]













/-- The factor congruence: N | (x² - y²). -/
def FactorCongruence (N x y : ℤ) : Prop := N ∣ (x ^ 2 - y ^ 2)



/-- Membership in the quadruple lattice L₄(N): x² + y² + z² ≡ 0 (mod N). -/
def InQuadLattice' (N : ℤ) (x y z : ℤ) : Prop :=
  N ∣ (x ^ 2 + y ^ 2 + z ^ 2)





/-- Three-square representation: N = x² + y² + z². -/
def IsThreeSquareRep' (N : ℤ) (x y z : ℤ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 = N







/-- The Lorentz form η = diag(1, 1, 1, -1) for O(3,1). -/
def lorentzEta' : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.diagonal ![1, 1, 1, -1]

/-- A matrix is in O(3,1;ℤ) if it preserves η. -/
def IsIntLorentz (M : Matrix (Fin 4) (Fin 4) ℤ) : Prop :=
  M.transpose * lorentzEta' * M = lorentzEta'







/-- The squared Euclidean norm of a 2D integer vector. -/
def sqNorm' (v : Fin 2 → ℤ) : ℤ := v 0 ^ 2 + v 1 ^ 2


