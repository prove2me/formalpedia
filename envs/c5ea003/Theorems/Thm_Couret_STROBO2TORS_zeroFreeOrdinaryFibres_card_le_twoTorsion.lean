-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_card_le_twoTorsion
-- name    : Couret.STROBO2TORS.zeroFreeOrdinaryFibres_card_le_twoTorsion
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:21.594683+00:00
-- url     : https://prove2.me/theorems/c2349c66-4484-4b0c-8254-61a0d3122a25
-- title:
--   Zero-free ordinary fibres are bounded by two-torsion size
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. For every nonempty zero-free ordinary fibre $R$,
--
--   $$|R|\le h.$$
--
--   Deleting zero-containing supports cannot increase the full ordinary-fibre size.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsMaximum.lean, lines 13–29; source file SHA-256 27aa6c02d9eb6f3a53aeb5b66640fa36aa2dc35441d6179ac79eb791d573ade2; theorem Couret.STROBO2TORS.zeroFreeOrdinaryFibres_card_le_twoTorsion

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

theorem zeroFreeOrdinaryFibres_card_le_twoTorsion
    (R : Finset (Finset G))
    (hR : R ∈ (zeroFreeOrdinaryFibres : Finset (Finset (Finset G)))) :
    R.card ≤ (twoTorsion : Finset G).card := by sorry








end Finite
end Couret.STROBO2TORS
