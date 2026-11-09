-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Eighth_reflection_image
-- name    : Couret.InterIA.Catalogue.Eighth.reflection_image
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:47:45.306826+00:00
-- url     : https://prove2.me/theorems/39c73532-00ea-49ad-98d9-a8665e0539ff
-- title:
--   reflection image
-- statement:
--   For all natural n,q with n=8q and c,d∈ℤ/nℤ such that c∈{2q,6q} and d∈{3q,7q}, the image of the finite set {c,d,0,4q} under z↦−z+c+d is exactly {c,d,q,5q}. Repeated elements count once; q=n=0 is allowed, with ambient ring ℤ.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/EighthReflection.lean, lines 30–58; source file SHA-256 bd7acf8c9a6c896c438b46b8ac15c560a3b57bf2c810b4f0886ebc95a04eecf8; theorem Couret.InterIA.Catalogue.Eighth.reflection_image

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
import Theorems.Thm_Couret_InterIA_Catalogue_Eighth_common_sum_cases
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Eighth
open Finset Couret.InterIA.NormalForm

theorem reflection_image (n q : ℕ) (hn : n=8*q) (c d : ZMod n)
    (hc : c=2 • (q : ZMod n) ∨ c=6 • (q : ZMod n))
    (hd : d=3 • (q : ZMod n) ∨ d=7 • (q : ZMod n)) :
    ({c,d,0,4 • (q : ZMod n)} : Finset (ZMod n)).image (fun z => -z+c+d)=
      {c,d,(q : ZMod n),5 • (q : ZMod n)} := by sorry






end Couret.InterIA.Catalogue.Eighth
