-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_fibre_card_le_two_pow_of_separating_bank
-- name    : Couret.STROBO2TORS.recoh_fibre_card_le_two_pow_of_separating_bank
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:03:02.478907+00:00
-- url     : https://prove2.me/theorems/345e45ee-2c29-4851-ae16-53fc1e6c3cd8
-- title:
--   A bank of k character readings separates at most two-to-k fibre members
-- statement:
--   Let $G$ be an abelian group, $R_S(z)$ the ordered pair-sum count of a support $S$, $P_\chi(S)=\sum_{s\in S}\chi(s)$, and $F(S)=\{T:|T|=3,R_T=R_S\}$. Put $H=G[2]$. Assume $G$ finite. If $k$ complex additive characters separate the full fibre $F(S)$, then
--
--   $$|F(S)|\le2^k.$$
--
--   The support $S$ is arbitrary, and the fibre may be empty.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohFibreLower.lean, lines 39–72; source file SHA-256 25b4421c1b3f5d0b165e92effb04f9cec71c9084d67a55ff431cc52c867772ef; theorem Couret.STROBO2TORS.recoh_fibre_card_le_two_pow_of_separating_bank

import Aesop
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_eq_or_neg_of_square_eq
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

/-!
Information lower bound for a bank chosen after the labelled ordered
square is known.  Reconstructing means actual injectivity on the existing
finite square fibre.  The result applies to arbitrary complex characters,
including probes which vanish on that fibre.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem recoh_fibre_card_le_two_pow_of_separating_bank
    (S : Finset G) {k : ℕ} (bank : Fin k → AddChar G ℂ)
    (hsep : Set.InjOn
      (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
      (squareFibre S)) :
    (squareFibre S).card ≤ 2 ^ k := by sorry






end Couret.STROBO2TORS
