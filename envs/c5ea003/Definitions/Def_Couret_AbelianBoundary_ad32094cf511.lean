-- Prove2me | Definitions.Def_Couret_AbelianBoundary_ad32094cf511
-- name    : Couret_AbelianBoundary_ad32094cf511
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:56.998733+00:00
-- url     : https://prove2.me/theorems/75cb9ca7-7fec-49e0-b427-be595b80a8de
-- title:
--   Explicit four-point collision in a square of cyclic groups
-- statement:
--   Defines $G_4=(\mathbb Z/4\mathbb Z)^2$ and the finite sets $S=\{(0,0),(0,1),(1,0),(3,3)\}$ and $T=\{(0,0),(0,3),(1,1),(3,0)\}$. These are the concrete witnesses used for a four-point square-profile collision with singleton intersection.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-boundary-20261103/AbelianBoundary.lean; source file SHA-256 20b6936c6a495be9d966a8d0f5b874362f747e56efa3585823bc25fb7148aba0

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
abbrev G4 := ZMod 4 × ZMod 4
def S : Finset G4 := {(0,0),(0,1),(1,0),(3,3)}
def T : Finset G4 := {(0,0),(0,3),(1,1),(3,0)}






end Couret.InterIA.AbelianBoundary


