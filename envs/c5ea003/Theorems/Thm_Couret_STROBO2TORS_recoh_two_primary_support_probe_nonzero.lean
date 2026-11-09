-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_support_probe_nonzero
-- name    : Couret.STROBO2TORS.recoh_two_primary_support_probe_nonzero
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:56:57.320003+00:00
-- url     : https://prove2.me/theorems/81127955-d13a-4e09-a1de-4e99476a8d45
-- title:
--   A primary-two character has nonzero sum on every triple
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $R_S$ the ordered pair-sum count of a finite support, and $P_\chi(S)=\sum_{s\in S}\chi(s)$. Let $\chi$ be a complex additive character such that for every $x\in G$ some natural $n$ satisfies $\chi(x)^{2^n}=1$. For every support $S$ of size three,
--
--   $$P_\chi(S)\ne0.$$
--
--   The ambient group need not be finite and the allowed two-power order may depend on $x$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohOptimalBank.lean, lines 18–27; source file SHA-256 eefa340afa430ea5481039b5dcc716ba178daf20a3ab3a669e9ff87e2565a8d5; theorem Couret.STROBO2TORS.recoh_two_primary_support_probe_nonzero

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_three
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_triple_nonzero
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

theorem recoh_two_primary_support_probe_nonzero
    (chi : AddChar G ℂ)
    (hprimary : ∀ x : G, ∃ n : ℕ, (chi x) ^ (2 ^ n) = 1)
    (S : Finset G) (hS : S.card = 3) :
    recohSupportProbe chi S ≠ 0 := by sorry




variable [Fintype G]









end Couret.STROBO2TORS
