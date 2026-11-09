-- Prove2me | Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
-- name    : Couret_CayleyTwoColourSpectral_cff7591a9c5d
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:02:14.836907+00:00
-- url     : https://prove2.me/theorems/4b881a6c-dbf4-4fd7-a8d6-44ecd7759afb
-- title:
--   Rational Cayley and translation matrices
-- statement:
--   For a finite abelian group and support $S$, the rational Cayley matrix is its directed adjacency matrix. A translation matrix records the single shift by $t$. The doublet and translation-triple matrices combine these shifts; an additive parity $\varepsilon:G\to\mathbb Z/2$ supplies a rational sign $(-1)^{\varepsilon(x)}$. These definitions connect support convolution to matrix powers and characteristic polynomials.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourSpectral.lean; source file SHA-256 c35f0bcb235d6cfd9ce9cf16e4ece0a784c0c18ed967e268865d8a9c061aa16b

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

/-- Rational adjacency matrix of a directed Cayley relation, including loops. -/
def abelianCayleyMatrix (S : Finset G) : Matrix G G ℚ :=
  fun x y => if y - x ∈ S then 1 else 0

/-- The permutation matrix for the directed translation by t. -/
def abelianTranslationMatrix (t : G) : Matrix G G ℚ :=
  fun x y => if y = x + t then 1 else 0











/-- Signs associated with a supplied additive parity. -/
def abelianParitySign (ε : G →+ ZMod 2) (x : G) : ℚ :=
  if ε x = 0 then 1 else -1





end Couret.CayleyDoublet

namespace Couret.CayleyDoublet
open Couret.CayleySpectral
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
/-- The sum of the two translation matrices in the doublet. -/
def abelianDoubletMatrix (d h : G) : Matrix G G ℚ :=
  abelianTranslationMatrix d + abelianTranslationMatrix (d + h)















/-- A sum of three translations; equality with Finset adjacency needs distinct supports. -/
def abelianTranslationTriple (a d h : G) : Matrix G G ℚ :=
  abelianTranslationMatrix a + abelianTranslationMatrix (a + d) +
    abelianTranslationMatrix ((a + d) + h)























end Couret.CayleyDoublet

namespace Couret.CayleyDoublet

open Classical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



























end Couret.CayleyDoublet


