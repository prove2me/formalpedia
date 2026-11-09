-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_mem_exact_decoder_iff
-- name    : Couret.STROBO2TORS.recoh_mem_exact_decoder_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:34.181737+00:00
-- url     : https://prove2.me/theorems/f1308f5c-17e9-45e9-a650-0d23e3ac5c08
-- title:
--   Exact decoder membership is exact observational compatibility
-- statement:
--   Let $G$ be a finite abelian group. For a character $\chi:G\to\mathbb C$ write $P_\chi(S)=\sum_{x\in S}\chi(x)$, and for a bank $(\chi_i)$ write $\operatorname{Obs}(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S(z)$ counts ordered pairs from $S$ summing to $z$. The exact decoder of $(R,o)$ consists of all three-element supports $S$ with $\operatorname{Obs}(S)=(R,o)$. For any finite support $S$, bank, and observation $(R,o)$,
--
--   $$S\in\operatorname{ExactDecoder}(R,o)\Longleftrightarrow |S|=3\text{ and }\operatorname{Obs}(S)=(R,o).$$
--
--   This characterizes the semantic solution set independently of candidate-generation details.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCandidateDecoder.lean, lines 138–152; source file SHA-256 776f7f56ee0e11b95b74a89da277d67a6f783658f9375affe48c6fa12273ef52; theorem Couret.STROBO2TORS.recoh_mem_exact_decoder_iff

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

theorem recoh_mem_exact_decoder_iff {I : Type*}
    (bank : I → AddChar G ℂ) (obs : (G → ℕ) × (I → ℂ)) (S : Finset G) :
    S ∈ recohExactDecoder bank obs ↔
      S.card = 3 ∧ recohObservation bank S = obs := by sorry






end Couret.STROBO2TORS
