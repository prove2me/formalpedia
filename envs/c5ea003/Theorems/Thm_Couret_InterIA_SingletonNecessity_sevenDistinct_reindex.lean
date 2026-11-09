-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_sevenDistinct_reindex
-- name    : Couret.InterIA.SingletonNecessity.sevenDistinct_reindex
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:07:08.125054+00:00
-- url     : https://prove2.me/theorems/4761a58b-803d-4749-b9e0-e091ab0d0f05
-- title:
--   Injective reindexing preserves seven-label distinctness
-- statement:
--   Let $G$ be an abelian group. Let $0,x_0,\ldots,x_5$ be pairwise distinct and let $p:\{0,\ldots,5\}\to\{0,\ldots,5\}$ be injective. Then
--
--   $$0,x_{p(0)},\ldots,x_{p(5)}\text{ are pairwise distinct}.$$
--
--   This permits relabeling without losing the separation hypotheses.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/RelabelBasics.lean, lines 10–15; source file SHA-256 ad051970dc8003cca85b8ddbc013f1c47aae55ee0fcba53af030e41581191f05; theorem Couret.InterIA.SingletonNecessity.sevenDistinct_reindex

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
import Theorems.Thm_Couret_InterIA_SingletonNecessity_distinctLabels_of_injective_nonzero
import Theorems.Thm_Couret_InterIA_SingletonNecessity_nonzero_of_distinctLabels
import Theorems.Thm_Couret_InterIA_SingletonNecessity_sevenDistinct_injective
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem sevenDistinct_reindex (x : Fin 6 → G) (hd : SevenDistinct x)
    (p : Fin 6 → Fin 6) (hp : Function.Injective p) : SevenDistinct (reindex x p) := by sorry










end Couret.InterIA.SingletonNecessity
