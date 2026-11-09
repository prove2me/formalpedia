-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_tripleSupportsProfile_card
-- name    : Couret.STROBO2TORS.tripleSupportsProfile_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:43.718009+00:00
-- url     : https://prove2.me/theorems/79b164e2-9b7d-4ca6-923e-c006d38bfe55
-- title:
--   Number of triples with a specified two-torsion intersection
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. For $0\le j\le3$,
--
--   $$|\{S\subseteq G:|S|=3,\ |S\cap H|=j\}|=\binom hj\binom{N-h}{3-j}.$$
--
--   The binomial factors automatically vanish when there are too few available points.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFreeAll.lean, lines 478–500; source file SHA-256 57e0e6b2919f605519cfad328e82e56477cae03c002010fa3c4fd6a8c218120b; theorem Couret.STROBO2TORS.tripleSupportsProfile_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupportsProfile
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]





































/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/















/-! ## Binomial enumeration of profile supports -/

theorem tripleSupportsProfile_card (j : ℕ) (hj : j ≤ 3) :
    (tripleSupportsProfile (G := G) j).card =
      (twoTorsion : Finset G).card.choose j *
      ((Fintype.card G - (twoTorsion : Finset G).card).choose (3 - j)) := by sorry


end Finite
end Couret.STROBO2TORS
