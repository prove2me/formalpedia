-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_eq_or_neg_of_square_eq
-- name    : Couret.STROBO2TORS.recoh_support_probe_eq_or_neg_of_square_eq
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:55:58.102197+00:00
-- url     : https://prove2.me/theorems/2d71ce64-db2a-47eb-bfbd-2102666f0281
-- title:
--   Equal ordered squares determine each probe up to sign
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. For any complex additive character $\chi$ and finite supports $S,T$ with $Q_S=Q_T$, $$P_\chi(S)=P_\chi(T)\quad\text{or}\quad P_\chi(S)=-P_\chi(T).$$ Support sizes and probe nonvanishing are not assumed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSquareFourier.lean, lines 58–72; source file SHA-256 d945a6e2f58d516ec42667f54f80235d5d7aef6c8722194abaf14ac9355633e8; theorem Couret.STROBO2TORS.recoh_support_probe_eq_or_neg_of_square_eq

import Aesop
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_sq
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

/-!
The actual ordered convolution square determines the square of every
individual labelled complex character coefficient.  This is a finite-sum
identity for arbitrary supports, independent of the triple classification.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem recoh_support_probe_eq_or_neg_of_square_eq
    (chi : AddChar G ℂ) (S T : Finset G)
    (hsquare : ∀ z : G, orderedSquare S z = orderedSquare T z) :
    recohSupportProbe chi S = recohSupportProbe chi T ∨
      recohSupportProbe chi S = -recohSupportProbe chi T := by sorry


end Couret.STROBO2TORS
