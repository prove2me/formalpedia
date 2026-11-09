-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Eighth_reflection_affine
-- name    : Couret.InterIA.Catalogue.Eighth.reflection_affine
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:51:48.755211+00:00
-- url     : https://prove2.me/theorems/499853ce-6f5c-4bd5-bc9e-548df2c1c55a
-- title:
--   Affine reflection of eighth patterns
-- statement:
--   For natural numbers $n,q$ with $n=8q$ and $c,d\in R=\operatorname{ZMod}(n)$ satisfying $c\in\{2q,6q\}$ and $d\in\{3q,7q\}$, there exist a unit $u\in R^\times$ and $v\in R$ such that $u\{c,d,0,4q\}+v=\{c,d,q,5q\}$. The case $q=n=0$, giving singleton sets in $\mathbb Z$, is included.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/EighthReflection.lean, lines 71–80; source file SHA-256 bd7acf8c9a6c896c438b46b8ac15c560a3b57bf2c810b4f0886ebc95a04eecf8; theorem Couret.InterIA.Catalogue.Eighth.reflection_affine

import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
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
import Theorems.Thm_Couret_InterIA_Catalogue_Eighth_reflection_image
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Eighth
open Finset Couret.InterIA.NormalForm

theorem reflection_affine (n q : ℕ) (hn : n=8*q) (c d : ZMod n)
    (hc : c=2 • (q : ZMod n) ∨ c=6 • (q : ZMod n))
    (hd : d=3 • (q : ZMod n) ∨ d=7 • (q : ZMod n)) :
    AffineEquivalent ({c,d,0,4 • (q : ZMod n)} : Finset (ZMod n))
      {c,d,(q : ZMod n),5 • (q : ZMod n)} := by sorry


end Couret.InterIA.Catalogue.Eighth
