-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_typed_square_format_check_iff
-- name    : Couret.STROBO2TORS.recoh_typed_square_format_check_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:56:06.300482+00:00
-- url     : https://prove2.me/theorems/36f50461-0a7a-43ae-ad44-5073cd909bf8
-- title:
--   The typed square checker matches the format contract
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. For any finite list $E$ of pairs in $G\times\mathbb N$, $$\operatorname{check}_{\mathrm{square}}(E)=\mathrm{true}\iff\operatorname{Format}_{\mathrm{square}}(E).$$
--
--   The contract includes the explicit length, distinct-key, coefficient-range, total-count, and parity constraints of typed square input. Explicitly, the format requires between three and six entries, no repeated group keys, each coefficient between one and three, coefficient sum nine, and either one or three odd coefficients.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohTypedObservation.lean, lines 66–68; source file SHA-256 5e7a00f9666a5b8cb41765e60b981ccdb33bfeadfb65f8a536d67383af84ce84; theorem Couret.STROBO2TORS.recoh_typed_square_format_check_iff

import Aesop
import Definitions.Def_Couret_RecohTypedObservation_b23b2e33136b
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
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72

set_option autoImplicit false

/-!
Typed sparse input for the labelled ordered convolution square.

The coefficient function and its covering finite set are constructed from
the same list of position/count entries.  Their consistency is proved,
rather than supplied to the decoder.  The format validator expresses the
numeric checks performed by the Python square reader after coordinates and
integers have been parsed.  Syntactic JSON parsing is not part of this file.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [DecidableEq G]

theorem recoh_typed_square_format_check_iff (entries : List (G × ℕ)) :
    recohTypedSquareFormatCheck entries = true ↔ RecohTypedSquareFormat entries := by sorry








end Couret.STROBO2TORS
