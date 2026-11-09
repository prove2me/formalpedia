-- Prove2me | Theorems.Thm_Couret_InterIA_AbelianBoundary_square_collision
-- name    : Couret.InterIA.AbelianBoundary.square_collision
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:04:46.81145+00:00
-- url     : https://prove2.me/theorems/a367fc7c-dca1-4578-8503-43821bafa253
-- title:
--   A concrete four-point square collision
-- statement:
--   In $G=(\mathbb Z/4)^2$, put $S=\{(0,0),(0,1),(1,0),(3,3)\}$ and $T=\{(0,0),(0,3),(1,1),(3,0)\}$. Their ordered-sum counts agree at every group element: $$Q_S(z)=Q_T(z)\qquad(z\in G).$$
--
--   Here $Q_U(z)=|\{(x,y)\in U^2:x+y=z\}|$. This is the explicit finite boundary collision.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-boundary-20261103/AbelianBoundary.lean, lines 14–14; source file SHA-256 20b6936c6a495be9d966a8d0f5b874362f747e56efa3585823bc25fb7148aba0; theorem Couret.InterIA.AbelianBoundary.square_collision

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

theorem square_collision : ∀ z : G4, orderedSquare S z = orderedSquare T z := by sorry



end Couret.InterIA.AbelianBoundary
