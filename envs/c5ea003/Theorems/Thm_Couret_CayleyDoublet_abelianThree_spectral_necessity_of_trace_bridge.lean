-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_spectral_necessity_of_trace_bridge
-- name    : Couret.CayleyDoublet.abelianThree_spectral_necessity_of_trace_bridge
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:35:30.515922+00:00
-- url     : https://prove2.me/theorems/e3efe7cd-bc6d-461c-ae72-d2ff8d4c0bbf
-- title:
--   Conditional necessity of the exceptional-triple spectral criterion
-- statement:
--   Let $G$ be a finite abelian group. Write $S_+=\{a,a+d,a+d+h\}$, $S_-=\{a,a-d,a-d+h\}$ and $A_\pm(x,y)=1$ if $y-x\in S_\pm$, and zero otherwise. Assume $h\ne0$, $2h=0$, and $d+\langle h\rangle$ has order exactly three. Assume the explicit trace bridge: for every natural $n$, equality of the characteristic polynomials of $A_+$ and $A_-$ implies equality of their $n$th-power traces. If those characteristic polynomials agree, then
--
--   $$\langle a,h\rangle\ne G\quad\text{or}\quad |G/\langle h\rangle|\text{ is even}.$$
--
--   The trace bridge is a hypothesis of this statement.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourNecessity.lean#L131-L162, lines 131–162; source file SHA-256 7675ca2a1f08e8c6a20617d181810b5c2b6a4f0cffcf96b93678cb0bc9c7869d; theorem Couret.CayleyDoublet.abelianThree_spectral_necessity_of_trace_bridge

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_odd_trace_witness_of_odd_quotient
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

theorem abelianThree_spectral_necessity_of_trace_bridge (a d h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hbridge :
      ∀ n : ℕ,
        (abelianCayleyMatrix (AbelianSource a d h)).charpoly =
          (abelianCayleyMatrix (AbelianTarget a d h)).charpoly →
        Matrix.trace (abelianCayleyMatrix (AbelianSource a d h) ^ n) =
          Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ n))
    (hcospec :
      (abelianCayleyMatrix (AbelianSource a d h)).charpoly =
        (abelianCayleyMatrix (AbelianTarget a d h)).charpoly) :
    AddSubgroup.closure ({a, h} : Set G) ≠ ⊤ ∨
      Even (Nat.card (G ⧸ AddSubgroup.zmultiples h)) := by sorry




end Couret.CayleyDoublet
