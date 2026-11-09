-- Prove2me | Theorems.Thm_Couret_InterIA_C4m_infinite_family
-- name    : Couret.InterIA.C4m.infinite_family
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:48:38.616095+00:00
-- url     : https://prove2.me/theorems/ca035f10-331b-49f3-a9bb-de9f6937571a
-- title:
--   Four-point family
-- statement:
--   For every natural number $m\ge2$, in $\mathbb Z/(4m)\mathbb Z$ the sets $S=\{0,1,m,2m+1\}$ and $T=\{0,m,m+1,3m+1\}$ both have cardinality $4$; for every $z$ the numbers of ordered pairs in $S^2$ and $T^2$ summing to $z$ agree; and for every $u$ with $2u=0$, $\{s+u:s\in S\}\ne T$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/InteriaC4m.lean, lines 198–204; source file SHA-256 20922ec6a91e45da3f1620e9daf510fabaf675a094c698e2eb771ab1c3cc3c6c; theorem Couret.InterIA.C4m.infinite_family

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
import Theorems.Thm_Couret_InterIA_C4m_encoded_squares_equal
import Theorems.Thm_Couret_InterIA_C4m_entries_distinct
import Theorems.Thm_Couret_InterIA_C4m_no_two_torsion_translate
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

theorem infinite_family (m : ℕ) (hm : 2 ≤ m) :
    (T m).card = 4 ∧ (U m).card = 4 ∧
    (∀ z, orderedSquare (T m) z = orderedSquare (U m) z) ∧
    (∀ u, u+u=0 → translateSupport (T m) u ≠ U m) := by sorry



end Couret.InterIA.C4m
