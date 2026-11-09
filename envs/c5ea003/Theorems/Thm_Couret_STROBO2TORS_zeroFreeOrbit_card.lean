-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrbit_card
-- name    : Couret.STROBO2TORS.zeroFreeOrbit_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:48:14.973137+00:00
-- url     : https://prove2.me/theorems/a2e49e4a-b29b-4995-b377-0d891735f6cd
-- title:
--   Size of a zero-free two-torsion orbit
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For any three-element support $S$, $$|\operatorname{Orb}_H^\circ(S)|=h-|S\cap H|.$$
--
--   The removed orbit elements are precisely those placing a two-torsion point at zero.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsCardinality.lean, lines 376–395; source file SHA-256 43bb7bc977683362729a3aa2f7c214abefd9138f3283fb79ee93f0a1da784093; theorem Couret.STROBO2TORS.zeroFreeOrbit_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_injective_on_two_torsion
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrbit_image
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























section Finite

variable [Fintype G]

theorem zeroFreeOrbit_card (S : Finset G) (hS : S.card = 3) :
    (zeroFreeOrbit S).card = (twoTorsion : Finset G).card -
      (S ∩ (twoTorsion : Finset G)).card := by sorry







/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/























end Finite
end Couret.STROBO2TORS
