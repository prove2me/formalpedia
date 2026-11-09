-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_exists_reconstructing_bank_rank_sum
-- name    : Couret.STROBO2TORS.recoh_exists_reconstructing_bank_rank_sum
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:28:08.337815+00:00
-- url     : https://prove2.me/theorems/bdb80d40-95f0-4f9d-97df-85f9f4340394
-- title:
--   A bank of torsion-rank sum reconstructs triples
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. Assume $G$ finite with $|H|=2^r$, $|K|=3^s$ for natural $r,s$. There exists a bank $B$ of exactly $r+s$ characters such that $$S\mapsto\mathcal O_B(S)$$ is injective on three-element supports. Zero ranks are allowed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohOptimalBank.lean, lines 44–69; source file SHA-256 eefa340afa430ea5481039b5dcc716ba178daf20a3ab3a669e9ff87e2565a8d5; theorem Couret.STROBO2TORS.recoh_exists_reconstructing_bank_rank_sum

import Aesop
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_reconstruction_of_separating_banks
import Theorems.Thm_Couret_STROBO2TORS_recoh_three_primary_characters_of_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_characters_of_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_support_probe_nonzero
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a

set_option autoImplicit false

/-!
The optimal size of a fixed bank of individual, labelled complex
Fourier coefficients, given the labelled ordered convolution square of a
three-element support.  Zero is allowed in the support.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]





variable [Fintype G]

theorem recoh_exists_reconstructing_bank_rank_sum
    (r s : ℕ)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (hcard3 : Nat.card (recohTorsionSubgroup (G := G) 3) = 3 ^ s) :
    ∃ bank : Fin (r + s) → AddChar G ℂ,
      Function.Injective (fun S : {S : Finset G // S.card = 3} =>
        recohObservation bank S.1) := by sorry








end Couret.STROBO2TORS
