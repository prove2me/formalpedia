-- Prove2me | Theorems.Thm_Catalog_Combinatorics_RotaBasis_cross_pairing_fin_two
-- name    : Catalog.Combinatorics.RotaBasis.cross_pairing_fin_two
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:03:02.877479+00:00
-- url     : https://prove2.me/theorems/67db7e32-a068-4821-b9d2-792a90cb3c2c
-- title:
--   The two-by-two exchange lemma underlying the rank-two case.
-- statement:
--   The two-by-two exchange lemma underlying the rank-two case.
--
--   ```lean
--   theorem Catalog.Combinatorics.RotaBasis.cross_pairing_fin_two(a b c d : V)
--       (hab : LinearIndependent K (![a, b] : Fin 2 → V))
--       (hcd : LinearIndependent K (![c, d] : Fin 2 → V)) :
--       (LinearIndependent K (![a, c] : Fin 2 → V) ∧
--         LinearIndependent K (![b, d] : Fin 2 → V)) ∨
--       (LinearIndependent K (![a, d] : Fin 2 → V) ∧
--         LinearIndependent K (![b, c] : Fin 2 → V)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/RotaBasisSmallRanks.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/RotaBasisSmallRanks.lean#L54

-- Thm stub generated from Combinatorics/RotaBasisSmallRanks.lean
import Mathlib
import Definitions.Def_Combinatorics_RotaBasisSmallRanks

/-!
# Rota's basis conjecture in ranks one and two

Rota's basis conjecture is open in full generality.  This file gives a faithful
formalization using Mathlib's `Basis` and proves the conjecture for one and two
bases.  An arrangement records that every row is a permutation of the given
basis and that every column is linearly independent.  Since the columns have
exactly as many entries as the ambient dimension, `columnBasis` upgrades each
column to a Mathlib `Basis`.
-/

open Catalog.Combinatorics.RotaBasis

open Module

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

theorem Catalog.Combinatorics.RotaBasis.cross_pairing_fin_two(a b c d : V)
    (hab : LinearIndependent K (![a, b] : Fin 2 → V))
    (hcd : LinearIndependent K (![c, d] : Fin 2 → V)) :
    (LinearIndependent K (![a, c] : Fin 2 → V) ∧
      LinearIndependent K (![b, d] : Fin 2 → V)) ∨
    (LinearIndependent K (![a, d] : Fin 2 → V) ∧
      LinearIndependent K (![b, c] : Fin 2 → V)) := by sorry
