-- Prove2me | Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
-- name    : Couret_AffineEquivalenceTransport_fe8e73389d60
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:12:23.55075+00:00
-- url     : https://prove2.me/theorems/8b21c732-bac4-4f8e-8121-788f8e24497f
-- title:
--   Affine equivalence transport interface
-- statement:
--   An import and namespace interface for affine-equivalence transport on finite subsets of $\operatorname{ZMod}(n)$. The imported affine relation means that $T=uS+v$ for some unit $u$ and element $v$. This file adds no mathematical definition or theorem.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AffineEquivalenceTransport.lean; source file SHA-256 317b8b661cceb15b156cd289602ed84565c6a27bf8af9028f7e0389c60f5aab8

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_AffineParameterControls_321393084939

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.AffineTransport
open Finset Couret.InterIA.NormalForm













end Couret.InterIA.Catalogue.AffineTransport


