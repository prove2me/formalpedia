-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_odd_quotient_return
-- name    : Couret.CayleyDoublet.abelianThree_odd_quotient_return
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:58:53.59806+00:00
-- url     : https://prove2.me/theorems/cc38a9a7-6a17-438c-be68-e13935efc720
-- title:
--   Odd return to either sign in an odd cyclic quotient
-- statement:
--   Let $G$ be a finite abelian group. Let $a,d,h\in G$. If $a,h$ generate $G$ and $|G/\langle h\rangle|$ is odd, there exists an odd natural number $n$ such that
--
--   $$na+d\in\langle h\rangle\quad\text{or}\quad na-d\in\langle h\rangle.$$
--
--   No order-three or half-turn condition is imposed in this lemma.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourNecessity.lean#L80-L103, lines 80–103; source file SHA-256 7675ca2a1f08e8c6a20617d181810b5c2b6a4f0cffcf96b93678cb0bc9c7869d; theorem Couret.CayleyDoublet.abelianThree_odd_quotient_return

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelian_quotient_zmultiples_generator_of_pair
import Theorems.Thm_Couret_CayleyNecessity_odd_multiple_or_neg_of_cyclic
import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d

/-!
COU-20 — research branch only, spectral necessity work in progress.

This file is deliberately separate from the certified Core/Family/Abelian/
Spectral/Parity modules. It does not claim a new Lean or GitHub Actions
certificate until it has been compiled against the pinned toolchain.

The cyclic lemma below produces an odd *discriminating* exponent. It is
slightly more general than the canonical candidate |Q|/3: its exponent
need not be the least such one. Directed adjacency and loops are untouched.

The generic rational charpoly-to-all-power-traces theorem is NOT assumed as
proved. The final assembly is explicitly conditional on that missing bridge.
-/

set_option autoImplicit false
noncomputable section

open Matrix

namespace Couret.CayleyNecessity





end Couret.CayleyNecessity

namespace Couret.CayleyDoublet

open Couret.CayleyNecessity

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem abelianThree_odd_quotient_return (a d h : G)
    (hcyc : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h))) :
    ∃ n : ℕ, Odd n ∧
      (n • a + d ∈ AddSubgroup.zmultiples h ∨
       n • a - d ∈ AddSubgroup.zmultiples h) := by sorry










end Couret.CayleyDoublet
