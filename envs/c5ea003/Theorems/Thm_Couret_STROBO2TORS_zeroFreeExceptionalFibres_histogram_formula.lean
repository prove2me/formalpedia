-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_histogram_formula
-- name    : Couret.STROBO2TORS.zeroFreeExceptionalFibres_histogram_formula
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:30:56.832201+00:00
-- url     : https://prove2.me/theorems/f6849701-decf-4f71-a0f3-ee8525119650
-- title:
--   The zero-free exceptional-fibre histogram
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Let $p=(t-1)/2$ and $\mathcal E^*=\{F^*:F\text{ exceptional}\}$. For each $k\in\mathbb N$,
--
--   $$|\{R\in\mathcal E^*:|R|=k\}|=\mathbf1_{k=2h-2}3(h-1)p+\mathbf1_{k=2h}(D-3)(h-1)p.$$
--
--   This formula includes $k=0$ and uses truncated natural subtraction.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFreeAll.lean, lines 214–247; source file SHA-256 57e0e6b2919f605519cfad328e82e56477cae03c002010fa3c4fd6a8c218120b; theorem Couret.STROBO2TORS.zeroFreeExceptionalFibres_histogram_formula

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_full_card
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_only_two_sizes
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_reduced_card
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem zeroFreeExceptionalFibres_histogram_formula (k : ℕ) :
    ((zeroFreeExceptionalFibres : Finset (Finset (Finset G))).filter
      (fun R => R.card = k)).card =
    (if k = 2 * (twoTorsion : Finset G).card - 2 then
      3 * ((twoTorsion : Finset G).card - 1) *
        (threeSignPairs : Finset (Finset G)).card else 0) +
    (if k = 2 * (twoTorsion : Finset G).card then
      ((doublingImages : Finset G).card - 3) *
        ((twoTorsion : Finset G).card - 1) *
        (threeSignPairs : Finset (Finset G)).card else 0) := by sorry






/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/















/-! ## Binomial enumeration of profile supports -/













end Finite
end Couret.STROBO2TORS
