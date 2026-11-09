-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_supportRight_reindex
-- name    : Couret.InterIA.SingletonNecessity.supportRight_reindex
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:05:49.724557+00:00
-- url     : https://prove2.me/theorems/d438bc84-7f01-45e4-817d-7a5bb715ad00
-- title:
--   Reindexing the right triple preserves its support
-- statement:
--   Let $G$ be an abelian group. Let $x_0,\ldots,x_5\in G$ and let $p$ be a map on their six indices such that $p(\{3,4,5\})=\{3,4,5\}$. Then
--
--   $$\{0,x_{p(3)},x_{p(4)},x_{p(5)}\}=\{0,x_3,x_4,x_5\}.$$
--
--   This transports support data under a triple-preserving reindexing.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/RelabelBasics.lean, lines 33–39; source file SHA-256 ad051970dc8003cca85b8ddbc013f1c47aae55ee0fcba53af030e41581191f05; theorem Couret.InterIA.SingletonNecessity.supportRight_reindex

import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
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
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem supportRight_reindex (x : Fin 6 → G) (p : Fin 6 → Fin 6)
    (hp : ({3,4,5}:Finset (Fin 6)).image p={3,4,5}) :
    supportRight (reindex x p)=supportRight x := by sorry


end Couret.InterIA.SingletonNecessity
