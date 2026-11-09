-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_reflection_supports_distinct
-- name    : Couret.STROBO2TORS.recoh_reflection_supports_distinct
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:43:39.579198+00:00
-- url     : https://prove2.me/theorems/c81b6791-1b2d-4136-bfc0-b94417a7a183
-- title:
--   Nonzero three-torsion gives distinct reflected supports
-- statement:
--   Let $G$ be an abelian group. Let $v,d\in G$ satisfy $v\ne0$, $3v=0$, and $2d=0$. Then
--
--   $$\{0,v,v+d\}\ne\{0,-v,-v+d\}.$$
--
--   This remains true for $d=0$, when these finite supports have only two elements.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohFourierBridge.lean, lines 112–133; source file SHA-256 162c4aac6224640abce8987d230b6cd34d69fa584578b00550229ed923853089; theorem Couret.STROBO2TORS.recoh_reflection_supports_distinct

import Aesop
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
RECOH/STROBO Fourier bridge -- bounded formalization layer, 2026-10-14.

This file reuses the already compiled STROBO classification/ordered-square
definitions instead of declaring another square or accepting an unproved
classification. It formalizes the collision witness and the *algebraic*
condition under which one character probe cannot distinguish the pair.

IMPORTANT BOUNDARY:
  * no theorem B(G) = r+s is claimed in this file;
  * the finite-rank/character-existence arguments still need a Lean proof;
  * complex Fourier characters are not assumed merely from ring functions;
  * no analytic, prime-race, novelty or publication claim.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_reflection_supports_distinct
    (v d : G) (hv0 : v ≠ 0)
    (hv3 : (v + v) + v = 0)
    (hd2 : d + d = 0) :
    ({0, v, v + d} : Finset G) ≠ {0, -v, -v + d} := by sorry




end Couret.STROBO2TORS
