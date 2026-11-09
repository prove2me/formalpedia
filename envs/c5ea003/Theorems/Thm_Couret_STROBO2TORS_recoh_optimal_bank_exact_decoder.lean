-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_optimal_bank_exact_decoder
-- name    : Couret.STROBO2TORS.recoh_optimal_bank_exact_decoder
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:56:20.684923+00:00
-- url     : https://prove2.me/theorems/af31a282-0ebe-4440-8c86-ced101cc4cfa
-- title:
--   An optimal bank has singleton exact decoding
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. Assume $G$ finite, $|H|=2^r$, $|K|=3^s$, and $|G|\ge3$. There is a bank $B$ of size $b(r,s)$ such that for every three-element support $S$, $$D_B(\mathcal O_B(S))=\{S\},\qquad b(r,s)=\begin{cases}0&r=0,\\r+s&r>0.\end{cases}$$
--
--   The exact decoder therefore recovers every actual triple from its observation.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCandidateDecoder.lean, lines 173–184; source file SHA-256 776f7f56ee0e11b95b74a89da277d67a6f783658f9375affe48c6fa12273ef52; theorem Couret.STROBO2TORS.recoh_optimal_bank_exact_decoder

import Aesop
import Definitions.Def_Couret_RecohCandidateDecoder_966deca9afb6
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_exact_decoder_singleton
import Theorems.Thm_Couret_STROBO2TORS_recoh_optimal_bank_size
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883

set_option autoImplicit false

/-!
Structured candidates for exact RECOH reconstruction.

For a genuine triple S = {a,b,c}, its three distinct off-diagonal sums
E = {a+b,a+c,b+c} belong to the support of the ordered square.  With
sigma = a+b+c, they satisfy sum E = sigma+sigma and S = sigma-E.
This supplies a complete candidate generator using only the input square.

The finite candidate generator uses decidable group operations.  The exact
complex-character filter below is explicitly noncomputable: this module
certifies its mathematical result, not an executable representation of
complex numbers or a refinement of a separate Python implementation.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]







variable [Fintype G]

theorem recoh_optimal_bank_exact_decoder
    (r s : ℕ)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (hcard3 : Nat.card (recohTorsionSubgroup (G := G) 3) = 3 ^ s)
    (hG3 : 3 ≤ Fintype.card G) :
    ∃ bank : Fin (recohOptimalBudget r s) → AddChar G ℂ,
      ∀ S : Finset G, S.card = 3 →
        recohExactDecoder bank (recohObservation bank S) = {S} := by sorry


end Couret.STROBO2TORS
