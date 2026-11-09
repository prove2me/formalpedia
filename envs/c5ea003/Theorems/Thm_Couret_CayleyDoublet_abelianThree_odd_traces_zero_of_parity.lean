-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_odd_traces_zero_of_parity
-- name    : Couret.CayleyDoublet.abelianThree_odd_traces_zero_of_parity
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:31:11.695868+00:00
-- url     : https://prove2.me/theorems/b130735a-db34-4679-a342-0d10d12a5466
-- title:
--   Odd traces vanish for the parity-separated triple pair
-- statement:
--   Let $G$ be a finite abelian group. Write $S_+=\{a,a+d,a+d+h\}$, $S_-=\{a,a-d,a-d+h\}$ and $A_\pm(x,y)=1$ if $y-x\in S_\pm$, and zero otherwise. Let $\varepsilon:G\to\mathbb Z/2\mathbb Z$ be additive, with $\varepsilon(a)=1$ and $\varepsilon(d)=\varepsilon(h)=0$. For every odd natural number $n$,
--
--   $$\operatorname{tr}(A_+^n)=\operatorname{tr}(A_-^n)=0.$$
--
--   No half-turn or quotient-order condition is needed for this parity consequence.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourSpectral.lean#L647-L660, lines 647–660; source file SHA-256 c35f0bcb235d6cfd9ce9cf16e4ece0a784c0c18ed967e268865d8a9c061aa16b; theorem Couret.CayleyDoublet.abelianThree_odd_traces_zero_of_parity

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianCayleyMatrix_parity_sign
import Theorems.Thm_Couret_CayleySpectral_trace_pow_eq_zero_of_odd_of_involution
import Definitions.Def_Couret_CayleyTwoColourAbelian_32e780a833c0

/-!
COU-20 — finite directed spectral bridge (17 October 2026).

This file connects finite-support convolution to the actual rational adjacency
matrices, proves cospectrality for a supplied additive parity and for the
already certified nongeneration branch, and proves exact odd-power and trace
difference formulas. Translation sums are identified with Finset adjacency
only after distinctness has been derived from the exact quotient order.

The construction of parity from quotient cardinality and the full spectral
classification are not asserted by these conditional spectral corollaries.
No undirected-graph extension, independent human review, release or priority
claim is made here. The preceding isomorphism dichotomy is imported unchanged.
-/

set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace Couret.CayleySpectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

















end Couret.CayleySpectral
namespace Couret.CayleySpectral
/-! An exact odd-power identity, valid in every unital associative ring. -/






















end Couret.CayleySpectral

namespace Couret.CayleyDoublet

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





















end Couret.CayleyDoublet

namespace Couret.CayleyDoublet
open Couret.CayleySpectral
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]








































end Couret.CayleyDoublet

namespace Couret.CayleyDoublet

open Classical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem abelianThree_odd_traces_zero_of_parity
    (a d h : G) (ε : G →+ ZMod 2)
    (ha : ε a = 1) (hd : ε d = 0) (hh : ε h = 0) (n : ℕ) (hn : Odd n) :
    Matrix.trace (abelianCayleyMatrix (AbelianSource a d h) ^ n) = 0 ∧
      Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ n) = 0 := by sorry






end Couret.CayleyDoublet
