-- Prove2me | Theorems.Thm_Couret_InterIA_AbelianBoundary_source_card
-- name    : Couret.InterIA.AbelianBoundary.source_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:04:37.419442+00:00
-- url     : https://prove2.me/theorems/ad5160ff-8e14-4be9-a9e8-e85e0009172c
-- title:
--   The explicit boundary witness has four elements
-- statement:
--   In $G_4=(\mathbb Z/4\mathbb Z)^2$, let $S=\{(0,0),(0,1),(1,0),(3,3)\}$. Then
--
--   $$|S|=4.$$
--
--   This checks the size of the explicit singleton-collision witness.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-boundary-20261103/AbelianBoundary.lean, lines 11–11; source file SHA-256 20b6936c6a495be9d966a8d0f5b874362f747e56efa3585823bc25fb7148aba0; theorem Couret.InterIA.AbelianBoundary.source_card

import Definitions.Def_Couret_AbelianBoundary_ad32094cf511
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret.InterIA.AbelianBoundary
open Finset Couret.InterIA.Parity

theorem source_card : S.card = 4 := by sorry






end Couret.InterIA.AbelianBoundary
