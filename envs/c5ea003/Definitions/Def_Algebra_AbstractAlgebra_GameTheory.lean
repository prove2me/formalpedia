-- Prove2me | Definitions.Def_Algebra_AbstractAlgebra_GameTheory
-- name    : Algebra_AbstractAlgebra_GameTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:04:58.793617+00:00
-- url     : https://prove2.me/theorems/a5d07f06-eb8c-446c-a684-df1b6e7db31a
-- title:
--   Aether Catalog definitions — Algebra_AbstractAlgebra_GameTheory
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.AbstractAlgebra.GameTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/AbstractAlgebra/GameTheory.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Algebra.GameTheory

Auto-generated from theorem catalog database.
Domain: Algebra
Declarations: 9
-/


/-- [Section: # CatalogBuild.Algebra.GameTheory
Auto-generated from theorem catalog database.
Domain: Algebra
Declarations: 9] -/
inductive PDAction' | Cooperate | Defect deriving DecidableEq, Fintype




/-- [Section: # CatalogBuild.Algebra.GameTheory
Auto-generated from theorem catalog database.
Domain: Algebra
Declarations: 9] -/
def pd_payoff' : PDAction' → PDAction' → ℤ × ℤ
  | .Cooperate, .Cooperate => (3, 3)
  | .Cooperate, .Defect => (0, 5)
  | .Defect, .Cooperate => (5, 0)
  | .Defect, .Defect => (1, 1)












def mp_payoff' : Bool → Bool → ℤ
  | true, true => 1
  | true, false => -1
  | false, true => -1
  | false, false => 1


