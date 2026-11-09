-- Prove2me | Theorems.Thm_Couret_InterIA_AbelianBoundary_unrestricted_even_obstruction_false
-- name    : Couret.InterIA.AbelianBoundary.unrestricted_even_obstruction_false
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:48:31.614067+00:00
-- url     : https://prove2.me/theorems/f2f612ac-33aa-4d10-87a8-467572ed0bf3
-- title:
--   Even support size does not exclude singleton-intersection collisions
-- statement:
--   For a finite subset $A$ of an abelian group, let $R_A(z)=|\{(a,b)\in A^2:a+b=z\}|$. In $G_4=(\mathbb Z/4\mathbb Z)^2$, the claim that every even-sized support $A$ and every support $B$ with $R_A=R_B$ must satisfy $|A\cap B|\ne1$ is false:
--
--   $$\neg\forall A,B\subseteq G_4,\quad 2\mid |A|\Longrightarrow R_A=R_B\Longrightarrow |A\cap B|\ne1.$$
--
--   This is a counterexample to the unrestricted even-size obstruction.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-boundary-20261103/AbelianBoundary.lean, lines 19–24; source file SHA-256 20b6936c6a495be9d966a8d0f5b874362f747e56efa3585823bc25fb7148aba0; theorem Couret.InterIA.AbelianBoundary.unrestricted_even_obstruction_false

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
import Theorems.Thm_Couret_InterIA_AbelianBoundary_common_singleton
import Theorems.Thm_Couret_InterIA_AbelianBoundary_source_card
import Theorems.Thm_Couret_InterIA_AbelianBoundary_square_collision
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret.InterIA.AbelianBoundary
open Finset Couret.InterIA.Parity

theorem unrestricted_even_obstruction_false :
    ¬ (∀ A B : Finset G4, A.card % 2=0 →
      (∀ z, orderedSquare A z=orderedSquare B z) → (A ∩ B).card ≠ 1) := by sorry

end Couret.InterIA.AbelianBoundary
