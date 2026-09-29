-- Prove2me | solution 1 for Catalog.Combinatorics.RotaBasis.rota_basis_rank_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:17:41.907323+00:00
-- url     : https://prove2.me/submissions/0138fc4f-ea0f-4aa7-a351-2012f67d4a78

-- Sol generated from Combinatorics/RotaBasisSmallRanks.lean
import Mathlib
import Definitions.Def_Combinatorics_RotaBasisSmallRanks
import Theorems.Thm_Catalog_Combinatorics_RotaBasis_cross_pairing_fin_two

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








open Catalog.Combinatorics.RotaBasis in
theorem solution(B : Fin 2 → Basis (Fin 2) K V) :
    ∃ G, IsRotaArrangement B G := by
  set a := B 0 0
  set b := B 0 1
  set c := B 1 0
  set d := B 1 1
  have hab : LinearIndependent K (![a, b] : Fin 2 → V) := by
    have h : LinearIndependent K (B 0) := (B 0).linearIndependent
    simp only [a, b] at h ⊢
    convert h using 1
    ext i
    fin_cases i <;> rfl
  have hcd : LinearIndependent K (![c, d] : Fin 2 → V) := by
    have h : LinearIndependent K (B 1) := (B 1).linearIndependent
    simp only [c, d] at h ⊢
    convert h using 1
    ext i
    fin_cases i <;> rfl
  rcases cross_pairing_fin_two a b c d hab hcd with h₁ | h₂
  · use fun i j => B i j
    constructor
    · intro i
      use Equiv.refl (Fin 2)
      funext j
      simp
    · intro j
      fin_cases j <;> [convert h₁.1 using 1; convert h₁.2 using 1] <;>
        ext i <;> fin_cases i <;> rfl
  · use fun i j => B i (if i = 0 then j else if j = 0 then 1 else 0)
    constructor
    · intro i
      fin_cases i <;> simp
      · use Equiv.refl (Fin 2)
        funext j
        simp
      · use Equiv.swap 0 1
        funext j
        fin_cases j <;> simp
    · intro j
      fin_cases j <;> [convert h₂.1 using 1; convert h₂.2 using 1] <;>
        ext i <;> fin_cases i <;> simp [a, b, c, d]
