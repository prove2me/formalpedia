-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Eighth_common_sum_cases
-- name    : Couret.InterIA.Catalogue.Eighth.common_sum_cases
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:43.109432+00:00
-- url     : https://prove2.me/theorems/eb006f88-e809-4977-9cd8-ddcd755c81f5
-- title:
--   common sum cases
-- statement:
--   For all natural n,q with n=8q and c,d∈ℤ/nℤ, if c∈{2q,6q} and d∈{3q,7q}, then c+d∈{q,5q}. All integers in these sets are interpreted in the residue ring; q=0, n=0 is included, where the ring is ℤ and c=d=0.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/EighthReflection.lean, lines 10–25; source file SHA-256 bd7acf8c9a6c896c438b46b8ac15c560a3b57bf2c810b4f0886ebc95a04eecf8; theorem Couret.InterIA.Catalogue.Eighth.common_sum_cases

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
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Eighth
open Finset Couret.InterIA.NormalForm

theorem common_sum_cases (n q : ℕ) (hn : n=8*q) (c d : ZMod n)
    (hc : c=2 • (q : ZMod n) ∨ c=6 • (q : ZMod n))
    (hd : d=3 • (q : ZMod n) ∨ d=7 • (q : ZMod n)) :
    c+d=(q : ZMod n) ∨ c+d=5 • (q : ZMod n) := by sorry










end Couret.InterIA.Catalogue.Eighth
