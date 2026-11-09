-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_only_two_sizes
-- name    : Couret.STROBO2TORS.zeroFreeExceptionalFibres_only_two_sizes
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:44.192816+00:00
-- url     : https://prove2.me/theorems/31cfc67e-ed4f-4b52-b4c9-5c9365ed28c1
-- title:
--   Zero-free exceptional fibres have two possible sizes
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. Every $R\in\mathcal E^\circ$ satisfies $$|R|=2h-2\quad\text{or}\quad |R|=2h.$$
--
--   This is stated for the deduplicated zero-free exceptional family.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFreeAll.lean, lines 199–212; source file SHA-256 57e0e6b2919f605519cfad328e82e56477cae03c002010fa3c4fd6a8c218120b; theorem Couret.STROBO2TORS.zeroFreeExceptionalFibres_only_two_sizes

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_zeroFree_card
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem zeroFreeExceptionalFibres_only_two_sizes (R : Finset (Finset G))
    (hR : R ∈ (zeroFreeExceptionalFibres : Finset (Finset (Finset G)))) :
    R.card = 2 * (twoTorsion : Finset G).card - 2 ∨
      R.card = 2 * (twoTorsion : Finset G).card := by sorry








/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/















/-! ## Binomial enumeration of profile supports -/













end Finite
end Couret.STROBO2TORS
