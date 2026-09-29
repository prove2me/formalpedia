-- Prove2me | Definitions.Def_Algebra_GracefulStars
-- name    : Algebra_GracefulStars
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:17:35.061159+00:00
-- url     : https://prove2.me/theorems/c65c290e-c175-4f50-851e-cbb572c5c149
-- title:
--   Aether Catalog definitions — Algebra_GracefulStars
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.GracefulStars`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/GracefulStars.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_GracefulTrees

/-!
# Graceful labelings of stars

Stars form a basic infinite family of caterpillars.  This file proves directly that the
complete bipartite graph `K_{1,n}` is graceful.
-/

open Finset SimpleGraph
open GracefulTrees

namespace GracefulTrees

/-- Label the centre of `K_{1,n}` by zero and its leaves by `1,…,n`. -/
def starLabel (n : ℕ) : Unit ⊕ Fin n → ℕ
  | .inl _ => 0
  | .inr i => i.1 + 1





end GracefulTrees


