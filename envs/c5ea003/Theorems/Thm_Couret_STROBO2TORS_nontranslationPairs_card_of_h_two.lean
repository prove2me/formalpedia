-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_nontranslationPairs_card_of_h_two
-- name    : Couret.STROBO2TORS.nontranslationPairs_card_of_h_two
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:53:10.437196+00:00
-- url     : https://prove2.me/theorems/a1b57566-fc11-4f79-8eae-fecef2847f94
-- title:
--   Zero-free unordered nontranslation pairs when two-torsion has size two
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Assume $h=2$. The number of unordered pairs of zero-free three-element supports with equal ordered squares and no translation between them is
--
--   $$\frac{t-1}{2}\left((4(N/2)-12)+1\right).$$
--
--   The inner subtraction is truncated before adding one.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsPairCount.lean, lines 445–450; source file SHA-256 f6c997c461f640aab1856a21d5adfad3e6bfdbf876e67e5783b3ba87b26827cd; theorem Couret.STROBO2TORS.nontranslationPairs_card_of_h_two

import Aesop
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_doublingImages_card_division
import Theorems.Thm_Couret_STROBO2TORS_group_card_eq_h_mul_doublingImages
import Theorems.Thm_Couret_STROBO2TORS_orderedNontranslationPairs_card_eq_twice
import Theorems.Thm_Couret_STROBO2TORS_pairParameters_card
import Theorems.Thm_Couret_STROBO2TORS_pairRealization_image
import Theorems.Thm_Couret_STROBO2TORS_pairRealization_injective_on
import Theorems.Thm_Couret_STROBO2TORS_threeSignPairs_card_division
import Theorems.Thm_Couret_STROBO2TORS_threeTorsion_nonzero_card_eq_two_pairs
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]
































attribute [local instance] Classical.propDecidable

theorem nontranslationPairs_card_of_h_two (hh : (twoTorsion : Finset G).card=2) :
    (nontranslationPairs : Finset (Finset (Finset G))).card =
      (((threeTorsion : Finset G).card-1)/2) *
        (4 * (Fintype.card G / 2) - 12 + 1) := by sorry


end Finite
end Couret.STROBO2TORS
