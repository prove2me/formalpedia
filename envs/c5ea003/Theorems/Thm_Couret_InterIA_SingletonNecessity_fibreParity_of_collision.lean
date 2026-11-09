-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_fibreParity_of_collision
-- name    : Couret.InterIA.SingletonNecessity.fibreParity_of_collision
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:39.985551+00:00
-- url     : https://prove2.me/theorems/9e25f3ec-1f45-4831-8274-98458b47648a
-- title:
--   A singleton collision forces parity matching of the six doubles
-- statement:
--   For a finite subset $A$ of an abelian group, let $R_A(z)=|\{(a,b)\in A^2:a+b=z\}|$. Let $G$ be an abelian group, and let $x_0,\ldots,x_5\in G$ be such that $0,x_0,\ldots,x_5$ are pairwise distinct. Put $A=\{0,x_0,x_1,x_2\}$, $B=\{0,x_3,x_4,x_5\}$, $L=[x_0,x_1,x_2,x_0+x_1,x_0+x_2,x_1+x_2]$, and $R=[x_3,x_4,x_5,x_3+x_4,x_3+x_5,x_4+x_5]$. If $R_A=R_B$, then for every $z\in G$,
--
--   $$|\{i<3:2x_i=z\}|\equiv|\{3\le i<6:2x_i=z\}|\pmod2.$$
--
--   This is the diagonal parity constraint after removing the shared zero element.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/SquareExpansion.lean, lines 78–88; source file SHA-256 9bb0068b4b8d7143f97d46947e4be4105b05b8c1d63e1cf936d8c33c351a30cc; theorem Couret.InterIA.SingletonNecessity.fibreParity_of_collision

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
import Theorems.Thm_Couret_InterIA_SingletonNecessity_diagonal_parity_of_collision
import Theorems.Thm_Couret_InterIA_SingletonNecessity_nonzero_of_distinctLabels
import Theorems.Thm_Couret_InterIA_SingletonNecessity_sevenDistinct_injective
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem fibreParity_of_collision (x : Fin 6 → G) (hd : SevenDistinct x)
    (hs : ∀ z, orderedSquare (supportLeft x) z=orderedSquare (supportRight x) z) :
    FibreParity (fun i => x i+x i) := by sorry


end Couret.InterIA.SingletonNecessity
