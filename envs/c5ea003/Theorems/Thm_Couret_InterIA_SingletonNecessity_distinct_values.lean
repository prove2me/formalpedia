-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_distinct_values
-- name    : Couret.InterIA.SingletonNecessity.distinct_values
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:02:58.066264+00:00
-- url     : https://prove2.me/theorems/9dbfb6ad-7397-4aa8-b139-69d9c788a10f
-- title:
--   Seven distinct labels imply six distinct coordinates
-- statement:
--   Let $G$ be an abelian group. Let $x:\{0,\ldots,5\}\to G$. If $0,x_0,\ldots,x_5$ are pairwise distinct, then
--
--   $$x_i=x_j\Longrightarrow i=j.$$
--
--   This extracts ordinary coordinate injectivity from the seven-label condition.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/ConditionalNecessity.lean, lines 9–26; source file SHA-256 cb9bb017b413d40837c57c50cc3c78b5f8fc5f8253e41ffaffda5cd427f7047c; theorem Couret.InterIA.SingletonNecessity.distinct_values

import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_MatchingElimination_8675038abe55
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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_evaluation_basis
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.AbelianBoundary
variable {G : Type*} [AddCommGroup G]

theorem distinct_values (x : Fin 6 → G) (hd : DistinctLabels x) :
    Function.Injective x := by sorry






end Couret.InterIA.SingletonNecessity
