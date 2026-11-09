-- Prove2me | Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
-- name    : Couret_RelabelBasics_a474d20b9d5f
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:05.858347+00:00
-- url     : https://prove2.me/theorems/f81e3ca9-aa9d-4104-b76c-f89afe0e7961
-- title:
--   Reindexing six labeled group elements
-- statement:
--   For $x:\{0,\ldots,5\}\to G$ and an index map $p$ on the same set, define
--
--   $$\operatorname{reindex}(x,p)_i=x_{p(i)}.$$
--
--   The definition does not require $p$ to be a permutation; injectivity or triple-image conditions are supplied by the separate transport theorems.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/RelabelBasics.lean; source file SHA-256 ad051970dc8003cca85b8ddbc013f1c47aae55ee0fcba53af030e41581191f05

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

def reindex (x : Fin 6 → G) (p : Fin 6 → Fin 6) : Fin 6 → G := fun i => x (p i)











end Couret.InterIA.SingletonNecessity


