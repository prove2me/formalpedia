-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_square_supportRight
-- name    : Couret.InterIA.SingletonNecessity.square_supportRight
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:07:05.698199+00:00
-- url     : https://prove2.me/theorems/a132c8ac-fba5-49dc-a54e-92f7bbbb8642
-- title:
--   The square profile of a rooted four-point support
-- statement:
--   For a finite subset $A$ of an abelian group, let $R_A(z)=|\{(a,b)\in A^2:a+b=z\}|$. Let $G$ be an abelian group, and let $x_0,\ldots,x_5\in G$ be such that $0,x_0,\ldots,x_5$ are pairwise distinct. Put $A=\{0,x_0,x_1,x_2\}$, $B=\{0,x_3,x_4,x_5\}$, $L=[x_0,x_1,x_2,x_0+x_1,x_0+x_2,x_1+x_2]$, and $R=[x_3,x_4,x_5,x_3+x_4,x_3+x_5,x_4+x_5]$. For every $z\in G$, let $m_K(z)$ denote the multiplicity of $z$ in a list $K$. Then
--
--   $$R_B(z)=\mathbf1_{z=0}+m_{[2x_3,2x_4,2x_5]}(z)+2m_R(z).$$
--
--   All coincidences between the diagonal and off-diagonal sums retain their multiplicities.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/SquareExpansion.lean, lines 67–76; source file SHA-256 9bb0068b4b8d7143f97d46947e4be4105b05b8c1d63e1cf936d8c33c351a30cc; theorem Couret.InterIA.SingletonNecessity.square_supportRight

import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_nonzero_of_distinctLabels
import Theorems.Thm_Couret_InterIA_SingletonNecessity_sevenDistinct_injective
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem square_supportRight (x : Fin 6 → G) (hd : SevenDistinct x) (z : G) :
    orderedSquare (supportRight x) z =
      (if 0=z then 1 else 0) + [x 3+x 3,x 4+x 4,x 5+x 5].count z +
      2 * (sumTermsRight x).count z := by sorry




end Couret.InterIA.SingletonNecessity
