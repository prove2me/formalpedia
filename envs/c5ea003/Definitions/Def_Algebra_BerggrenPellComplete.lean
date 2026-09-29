-- Prove2me | Definitions.Def_Algebra_BerggrenPellComplete
-- name    : Algebra_BerggrenPellComplete
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:05:37.607853+00:00
-- url     : https://prove2.me/theorems/e684c4d6-58f3-4ff8-b6a2-a644b4ea8d97
-- title:
--   Aether Catalog definitions — Algebra_BerggrenPellComplete
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.BerggrenPellComplete`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/BerggrenPellComplete.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Speculative.BerggrenPellComplete

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 40
-/

/-- Berggren matrix B₂ -/
def B2 : Matrix (Fin 3) (Fin 3) ℤ := !![1, 2, 2; 2, 1, 2; 2, 2, 3]

/-- Iteratively apply B₂ starting from (3,4,5) -/
def B2iter : ℕ → ℤ × ℤ × ℤ
  | 0 => (3, 4, 5)
  | n + 1 =>
    let prev := B2iter n
    (prev.1 + 2 * prev.2.1 + 2 * prev.2.2,
     2 * prev.1 + prev.2.1 + 2 * prev.2.2,
     2 * prev.1 + 2 * prev.2.1 + 3 * prev.2.2)

/-- Extract hypotenuse -/
def B2hyp (n : ℕ) : ℤ := (B2iter n).2.2




























/-- The Pell numbers P_n satisfy x² - 2y² = 1 -/
def pellSeq : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (3 * (pellSeq n).1 + 4 * (pellSeq n).2,
              2 * (pellSeq n).1 + 3 * (pellSeq n).2)





-- Verify Pell equation x² - 2y² = 1


