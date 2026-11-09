-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_tripleSupportsProfile_ordinary_exceptional
-- name    : Couret.STROBO2TORS.tripleSupportsProfile_ordinary_exceptional
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:52.573874+00:00
-- url     : https://prove2.me/theorems/adb2dd01-087f-442d-bcb4-182f03641a78
-- title:
--   Each triple profile splits into ordinary and exceptional supports
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For every natural $j$, $$\mathcal S_{3,j}=\mathcal S_{\mathrm{ord},j}\cup\mathcal S_{\mathrm{exc},j}.$$
--
--   The profiles count intersection with $H$; out-of-range profiles are included.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsOrdinaryCount.lean, lines 128–143; source file SHA-256 36abdb7751662075f2a7470be2d1ccb52e577e35046510b06cdd5f29e66531f2; theorem Couret.STROBO2TORS.tripleSupportsProfile_ordinary_exceptional

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupportsProfile
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_h_or_two_h
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

theorem tripleSupportsProfile_ordinary_exceptional (j : ℕ) :
    (tripleSupportsProfile (G := G) j) =
      ordinarySupportsProfile j ∪ exceptionalSupportsProfile j := by sorry














/-! ## Exceptional-support strata through their unique parameters -/







/-! ## Arithmetic classification of each exceptional parameter profile -/







/-! ## First explicit exceptional parameter count (one two-torsion vertex) -/






/-! ## Second exceptional support profile via an involution on raw parameters -/













/-! ## Closed numerical counts of ordinary profile-one and profile-two fibres -/





end Finite
end Couret.STROBO2TORS
