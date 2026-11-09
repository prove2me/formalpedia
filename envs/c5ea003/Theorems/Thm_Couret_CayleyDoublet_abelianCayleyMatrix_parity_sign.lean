-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianCayleyMatrix_parity_sign
-- name    : Couret.CayleyDoublet.abelianCayleyMatrix_parity_sign
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:57:00.816703+00:00
-- url     : https://prove2.me/theorems/194436cd-bb4a-4f17-81e4-95f56751a28a
-- title:
--   Parity reverses across Cayley arcs
-- statement:
--   Let $G$ be a finite abelian group. Let $S\subseteq G$ and let $\varepsilon:G\to\mathbb Z/2\mathbb Z$ be additive and equal to one on every element of $S$. Define $\sigma(x)=1$ if $\varepsilon(x)=0$ and $-1$ otherwise. For vertices $x,y$ with a nonzero entry in the rational Cayley adjacency matrix,
--
--   $$\sigma(x)=-\sigma(y).$$
--
--   This supplies the sign change along every directed edge.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourSpectral.lean#L280-L295, lines 280–295; source file SHA-256 c35f0bcb235d6cfd9ce9cf16e4ece0a784c0c18ed967e268865d8a9c061aa16b; theorem Couret.CayleyDoublet.abelianCayleyMatrix_parity_sign

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
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

theorem abelianCayleyMatrix_parity_sign (S : Finset G) (ε : G →+ ZMod 2)
    (hS : ∀ s ∈ S, ε s = 1) (x y : G)
    (hne : abelianCayleyMatrix S x y ≠ 0) :
    abelianParitySign ε x = -abelianParitySign ε y := by sorry


end Couret.CayleyDoublet

namespace Couret.CayleyDoublet
open Couret.CayleySpectral
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]








































end Couret.CayleyDoublet

namespace Couret.CayleyDoublet

open Classical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



























end Couret.CayleyDoublet
