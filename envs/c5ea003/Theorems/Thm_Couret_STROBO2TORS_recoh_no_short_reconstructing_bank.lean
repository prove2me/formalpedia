-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_no_short_reconstructing_bank
-- name    : Couret.STROBO2TORS.recoh_no_short_reconstructing_bank
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:26:59.383502+00:00
-- url     : https://prove2.me/theorems/33417754-5e67-4c54-ad45-3f192d0589b2
-- title:
--   Fewer than the torsion-rank sum cannot reconstruct triples
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. Assume $G$ finite, $|H|=2^r$, $|K|=3^s$, $r>0$, and $|G|\ge3$. For every $k<r+s$ and every bank $B$ of $k$ complex characters, $$S\mapsto\mathcal O_B(S)\text{ is not injective on three-element supports}.$$
--
--   The positive binary rank is an explicit hypothesis.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohLowerBound.lean, lines 43–115; source file SHA-256 13a6eef82b24691dea82326ef99d8a4fd3ca6ddf05da19cda5211e7f7d912184; theorem Couret.STROBO2TORS.recoh_no_short_reconstructing_bank

import Aesop
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
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
import Theorems.Thm_Couret_STROBO2TORS_paired_support_card_three
import Theorems.Thm_Couret_STROBO2TORS_recoh_short_complex_character_bank_collision
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_three
import Theorems.Thm_Couret_STROBO2TORS_recoh_torsion_subgroup_nsmul
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a

set_option autoImplicit false

/-!
RECOH lower bound for the fixed labelled observation model.

The torsion groups are the actual subgroups G[2] and G[3]. Complex
character encodings are supplied by RecohComplexCharacterEncodings.
The sole size condition |G| >= 3 supplies a genuine three-point support.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_no_short_reconstructing_bank [Fintype G]
    (r s k : ℕ) (hr : 0 < r) (hk : k < r + s)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (hcard3 : Nat.card (recohTorsionSubgroup (G := G) 3) = 3 ^ s)
    (hG3 : 3 ≤ Fintype.card G) (bank : Fin k → AddChar G ℂ) :
    ¬ Function.Injective (fun S : {S : Finset G // S.card = 3} =>
      recohObservation bank S.1) := by sorry


end Couret.STROBO2TORS
