-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_exists_reconstructing_empty_bank
-- name    : Couret.STROBO2TORS.recoh_exists_reconstructing_empty_bank
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:28:04.152105+00:00
-- url     : https://prove2.me/theorems/8f0d0d3a-1a48-4ff2-a7b4-16a074dfc3df
-- title:
--   Trivial two-torsion admits an empty reconstructing bank
-- statement:
--   Let $G$ be a finite abelian group. For a character $\chi:G\to\mathbb C$ write $P_\chi(S)=\sum_{x\in S}\chi(x)$, and for a bank $(\chi_i)$ write $\operatorname{Obs}(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S(z)$ counts ordered pairs from $S$ summing to $z$. The exact decoder of $(R,o)$ consists of all three-element supports $S$ with $\operatorname{Obs}(S)=(R,o)$. If $|G[2]|=2^0=1$, there exists an empty bank for which
--
--   $$\operatorname{Obs}\text{ is injective on all three-element supports}.$$
--
--   Here the observation consists only of ordered-square data.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohOptimalBank.lean, lines 71–82; source file SHA-256 eefa340afa430ea5481039b5dcc716ba178daf20a3ab3a669e9ff87e2565a8d5; theorem Couret.STROBO2TORS.recoh_exists_reconstructing_empty_bank

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_square_injective_of_trivial_two_torsion
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_characters_of_card
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

theorem recoh_exists_reconstructing_empty_bank
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ 0) :
    ∃ bank : Fin 0 → AddChar G ℂ,
      Function.Injective (fun S : {S : Finset G // S.card = 3} =>
        recohObservation bank S.1) := by sorry






end Couret.STROBO2TORS
