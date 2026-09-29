-- Prove2me | Definitions.Def_EML_SPBExtended_BerggrenGenesis
-- name    : EML_SPBExtended_BerggrenGenesis
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:47.006433+00:00
-- url     : https://prove2.me/theorems/f7847727-2bd2-4436-a82d-a3e3d54005b3
-- title:
--   Aether Catalog definitions — EML_SPBExtended_BerggrenGenesis
-- statement:
--   Definition bundle for the Aether Catalog module `EML.SPBExtended.BerggrenGenesis`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/SPBExtended/BerggrenGenesis.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Pythagorean.Berggren.BerggrenGenesis

Auto-generated from theorem catalog database.
Domain: Pythagorean/Berggren
Declarations: 39
-/

/-- Berggren matrix A -/
def berg_A : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, -2, 2; 2, -1, 2; 2, -2, 3]

/-- Berggren matrix B -/
def berg_B : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 2, 2; 2, 1, 2; 2, 2, 3]

/-- Berggren matrix C -/
def berg_C : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-1, 2, 2; -2, 1, 2; -2, 2, 3]

/-- The swap matrix S that exchanges coordinates a and b -/
def berg_S : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 1]

/-- The vacuum triple (0, 1, 1) -/
def vacuum : Fin 3 → ℤ := ![0, 1, 1]

/-- The light triple (1, 0, 1) -/
def light : Fin 3 → ℤ := ![1, 0, 1]

/-- The first real triple (3, 4, 5) -/
def triple345 : Fin 3 → ℤ := ![3, 4, 5]

/-- The swapped first triple (4, 3, 5) -/
def triple435 : Fin 3 → ℤ := ![4, 3, 5]























/-- The Lorentz metric matrix Q = diag(1, 1, -1) -/
def lorentz_Q : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0; 0, 1, 0; 0, 0, -1]


