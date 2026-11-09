-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_fibre_rank_le_of_separating_bank
-- name    : Couret.STROBO2TORS.recoh_fibre_rank_le_of_separating_bank
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:17:25.844726+00:00
-- url     : https://prove2.me/theorems/b4ec06ef-3bcd-4081-be85-3277488be5da
-- title:
--   A separating bank must cover the binary fibre rank
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. Assume $G$ finite and $|F(S)|=2^r$. If a bank of $k$ characters has injective readings on $F(S)$, then $$r\le k.$$ Natural ranks zero and empty banks are included.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohFibreLower.lean, lines 74–87; source file SHA-256 25b4421c1b3f5d0b165e92effb04f9cec71c9084d67a55ff431cc52c867772ef; theorem Couret.STROBO2TORS.recoh_fibre_rank_le_of_separating_bank

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_fibre_card_le_two_pow_of_separating_bank
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

theorem recoh_fibre_rank_le_of_separating_bank
    (S : Finset G) (r : ℕ) (hcard : (squareFibre S).card = 2 ^ r)
    {k : ℕ} (bank : Fin k → AddChar G ℂ)
    (hsep : Set.InjOn
      (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
      (squareFibre S)) : r ≤ k := by sorry




end Couret.STROBO2TORS
