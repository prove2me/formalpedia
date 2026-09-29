-- Prove2me | Definitions.Def_Combinatorics_RotaBasisSmallRanks
-- name    : Combinatorics_RotaBasisSmallRanks
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:48:44.850289+00:00
-- url     : https://prove2.me/theorems/9532f21b-23e4-4897-9fbc-8c2343cd613a
-- title:
--   Aether Catalog definitions — Combinatorics_RotaBasisSmallRanks
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.RotaBasisSmallRanks`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/RotaBasisSmallRanks.lean by skeleton subtraction
import Mathlib

/-!
# Rota's basis conjecture in ranks one and two

Rota's basis conjecture is open in full generality.  This file gives a faithful
formalization using Mathlib's `Basis` and proves the conjecture for one and two
bases.  An arrangement records that every row is a permutation of the given
basis and that every column is linearly independent.  Since the columns have
exactly as many entries as the ambient dimension, `columnBasis` upgrades each
column to a Mathlib `Basis`.
-/

namespace Catalog.Combinatorics.RotaBasis

open Module

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A Rota arrangement: rows permute the supplied bases and columns are
linearly independent. -/
def IsRotaArrangement {n : ℕ} (B : Fin n → Basis (Fin n) K V)
    (G : Fin n → Fin n → V) : Prop :=
  (∀ i, ∃ e : Equiv.Perm (Fin n), G i = fun j => B i (e j)) ∧
    ∀ j, LinearIndependent K (fun i => G i j)

/-- Every column of a Rota arrangement canonically determines a basis. -/
noncomputable def columnBasis {n : ℕ} [NeZero n] (B : Fin n → Basis (Fin n) K V)
    (G : Fin n → Fin n → V) (hG : IsRotaArrangement B G) (j : Fin n) :
    Basis (Fin n) K V :=
  basisOfLinearIndependentOfCardEqFinrank (hG.2 j) (by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis (B 0), Fintype.card_fin])





end Catalog.Combinatorics.RotaBasis


