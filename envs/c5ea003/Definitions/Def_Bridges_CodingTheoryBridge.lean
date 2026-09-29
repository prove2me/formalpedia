-- Prove2me | Definitions.Def_Bridges_CodingTheoryBridge
-- name    : Bridges_CodingTheoryBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:59.625393+00:00
-- url     : https://prove2.me/theorems/c93e66fc-a2e7-41f2-9d70-ded4d2268d37
-- title:
--   Aether Catalog definitions — Bridges_CodingTheoryBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CodingTheoryBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CodingTheoryBridge.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Bridges.CodingTheoryBridge

Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 29
-/

noncomputable section

/-- Volume of a Hamming sphere of radius t in F_q^n. -/
def hammingVolume (n t q : ℕ) : ℕ :=
  (Finset.range (t + 1)).sum (fun i => n.choose i * (q - 1) ^ i)












/-- Gaussian integer norm: N(a + bi) = a² + b². -/
def gaussianNorm (a b : ℤ) : ℤ := a^2 + b^2





/-- Eisenstein integer norm: N(a+bω) = a²-ab+b². -/
def eisensteinNorm (a b : ℤ) : ℤ := a^2 - a*b + b^2



/-- The Cayley-Dickson dimensions: 1, 2, 4, 8. -/
def cayleyDicksonDimensions : List ℕ := [1, 2, 4, 8]




/-- Code rate R = k/n. -/
def codeRate (k n : ℕ) : ℚ := (k : ℚ) / (n : ℚ)





end


