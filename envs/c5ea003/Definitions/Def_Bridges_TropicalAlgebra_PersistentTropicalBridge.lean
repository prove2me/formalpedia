-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_PersistentTropicalBridge
-- name    : Bridges_TropicalAlgebra_PersistentTropicalBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:20.048509+00:00
-- url     : https://prove2.me/theorems/22a2af06-5c8d-4db0-8c37-38b2f3ce6592
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_PersistentTropicalBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.PersistentTropicalBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/PersistentTropicalBridge.lean by skeleton subtraction
import Mathlib

/-- A persistence interval with birth no later than death. -/
structure PersistenceInterval where
  birth : ℝ
  death : ℝ
  valid : birth ≤ death

/-- The lifetime of a persistence interval. -/
def PersistenceInterval.lifetime (I : PersistenceInterval) : ℝ := I.death - I.birth

/-- Distance from an interval endpoint pair to the diagonal. -/
noncomputable def diagonalDist (I : PersistenceInterval) : ℝ := I.lifetime / 2

/-! # CatalogBuild.Bridges.PersistentTropicalBridge

Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 20
-/

noncomputable section


/-- The L∞ distance between two persistence points.
d∞((b₁,d₁), (b₂,d₂)) = max(|b₁-b₂|, |d₁-d₂|). -/
def bottleneckPointDist (I J : PersistenceInterval) : ℝ :=
  max (|I.birth - J.birth|) (|I.death - J.death|)







/-- A tropical monomial. -/
structure TropicalMonomial where
  coefficient : ℝ
  degree : ℕ

/-- Tropical polynomial evaluation: p(x) = max_i (aᵢ + nᵢ · x). -/
def tropicalEval (monomials : List TropicalMonomial) (x : ℝ) : ℝ :=
  match monomials with
  | [] => 0
  | [m] => m.coefficient + m.degree * x
  | m :: rest => max (m.coefficient + m.degree * x) (tropicalEval rest x)





/-- The projection onto the diagonal. -/
def diagonalProjection (I : PersistenceInterval) : PersistenceInterval where
  birth := (I.birth + I.death) / 2
  death := (I.birth + I.death) / 2
  valid := le_refl _



/-- Significance of a loss landscape feature = its persistence. -/
def significance (f : PersistenceInterval) : ℝ := f.lifetime



end


