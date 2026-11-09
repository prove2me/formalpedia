-- Prove2me | Theorems.Thm_Couret_InterIA_C4m_two_torsion_iff
-- name    : Couret.InterIA.C4m.two_torsion_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:01.288742+00:00
-- url     : https://prove2.me/theorems/ace649f8-9e21-41f6-a05a-33972f576e1b
-- title:
--   two torsion iff
-- statement:
--   For every natural number $m≥2$ and $u∈ℤ/(4m)ℤ$, $u+u=0$ if and only if $u=0$ or $u=2m$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/InteriaC4m.lean, lines 135–165; source file SHA-256 20922ec6a91e45da3f1620e9daf510fabaf675a094c698e2eb771ab1c3cc3c6c; theorem Couret.InterIA.C4m.two_torsion_iff

import Aesop
import Definitions.Def_Couret_InteriaC4m_265d5cdb2807
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464

set_option autoImplicit false

noncomputable section

namespace Couret.InterIA.C4m
open Finset
open Couret.STROBO2TORS

/-!
Parametric, labelled ordered-square collisions in C_(4m), m >= 2.
The family originates in the coordinator's post-primary derivation in private
PR #333. This formalization makes no claim of novelty or provider autonomy.
`orderedSquare` and `translateSupport` are imported unchanged from STROBO,
the core used by the RECOH conditional orbit bridge. See PROVENANCE.json.
-/
















variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem two_torsion_iff (m : ℕ) (hm : 2 ≤ m) (u : ZMod (4*m)) :
    u + u = 0 ↔ u = 0 ∨ u = (2*m : ℕ) := by sorry











end Couret.InterIA.C4m
