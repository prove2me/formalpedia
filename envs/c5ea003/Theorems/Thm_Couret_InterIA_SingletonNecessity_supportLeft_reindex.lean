-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_supportLeft_reindex
-- name    : Couret.InterIA.SingletonNecessity.supportLeft_reindex
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:05:51.794137+00:00
-- url     : https://prove2.me/theorems/18c03330-d5d5-469e-bd0c-2e1ba7b88c65
-- title:
--   Left support is unchanged by a block-preserving reindexing
-- statement:
--   Let $G$ be an abelian group, $x:\{0,\ldots,5\}\to G$, and $p$ a self-map of those six indices whose image of $\{0,1,2\}$ is exactly $\{0,1,2\}$. Then $$\operatorname{supportLeft}(x\circ p)=\operatorname{supportLeft}(x).$$ No global injectivity of $p$ is assumed. Here $\operatorname{supportLeft}(x)=\{0,x_0,x_1,x_2\}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/RelabelBasics.lean, lines 25–31; source file SHA-256 ad051970dc8003cca85b8ddbc013f1c47aae55ee0fcba53af030e41581191f05; theorem Couret.InterIA.SingletonNecessity.supportLeft_reindex

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

theorem supportLeft_reindex (x : Fin 6 → G) (p : Fin 6 → Fin 6)
    (hp : ({0,1,2}:Finset (Fin 6)).image p={0,1,2}) :
    supportLeft (reindex x p)=supportLeft x := by sorry




end Couret.InterIA.SingletonNecessity
