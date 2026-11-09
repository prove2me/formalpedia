-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_spectral_equivalence_of_trace_bridge
-- name    : Couret.CayleyDoublet.abelianThree_spectral_equivalence_of_trace_bridge
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:50:24.815892+00:00
-- url     : https://prove2.me/theorems/92f97ffd-eddc-43d1-8e9f-1311f950308b
-- title:
--   Conditional spectral classification via a trace bridge
-- statement:
--   Let $G$ be a finite abelian group. Suppose $a,d,h\in G$, $2h=0$, $h\ne0$, and the image of $d$ in $G/\langle h\rangle$ has exact order three. Write $S=\{a,a+d,a+d+h\}$ and $T=\{a,a-d,a-d+h\}$, and let $A_U(x,y)=1$ if $y-x\in U$ and $0$ otherwise, with rational entries. Suppose $\langle a,d,h\rangle=G$. Assume also that equality of the two characteristic polynomials implies equality of $\operatorname{tr}(A_S^n)$ and $\operatorname{tr}(A_T^n)$ for every $n\in\mathbb N$. Then
--
--   $$\operatorname{charpoly}(A_S)=\operatorname{charpoly}(A_T)\quad\Longleftrightarrow\quad \langle a,h\rangle\ne G\ \text{or}\ |G/\langle h\rangle|\text{ is even}.$$
--
--   This combines the two sufficient spectral branches with a conditional necessity result.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourNecessity.lean#L164-L186, lines 164–186; source file SHA-256 7675ca2a1f08e8c6a20617d181810b5c2b6a4f0cffcf96b93678cb0bc9c7869d; theorem Couret.CayleyDoublet.abelianThree_spectral_equivalence_of_trace_bridge

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianThreeCospectral_of_nongeneration_or_even_quotient
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_spectral_necessity_of_trace_bridge
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

theorem abelianThree_spectral_equivalence_of_trace_bridge (a d h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hgen : AddSubgroup.closure ({a, d, h} : Set G) = ⊤)
    (hbridge :
      ∀ n : ℕ,
        (abelianCayleyMatrix (AbelianSource a d h)).charpoly =
          (abelianCayleyMatrix (AbelianTarget a d h)).charpoly →
        Matrix.trace (abelianCayleyMatrix (AbelianSource a d h) ^ n) =
          Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ n)) :
    ((abelianCayleyMatrix (AbelianSource a d h)).charpoly =
        (abelianCayleyMatrix (AbelianTarget a d h)).charpoly) ↔
      (AddSubgroup.closure ({a, h} : Set G) ≠ ⊤ ∨
       Even (Nat.card (G ⧸ AddSubgroup.zmultiples h))) := by sorry


end Couret.CayleyDoublet
