-- Prove2me | Theorems.Thm_Couret_InterIA_C4m_encoded_squares_equal
-- name    : Couret.InterIA.C4m.encoded_squares_equal
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:38:09.058685+00:00
-- url     : https://prove2.me/theorems/4620322a-dc38-4a2a-88b4-53de2ef29c27
-- title:
--   encoded squares equal
-- statement:
--   Work in the integer group ring of the stated additive group, with convolution multiplication; write e(a) for the function equal to 1 at a and 0 elsewhere, and I(E)=Σ(a∈E)e(a). For every natural number m≥2, in the group ring of ℤ/(4m)ℤ the square of I({0,1,m,2m+1}) equals the square of I({0,m,m+1,3m+1}).
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/InteriaC4m.lean, lines 107–126; source file SHA-256 20922ec6a91e45da3f1620e9daf510fabaf675a094c698e2eb771ab1c3cc3c6c; theorem Couret.InterIA.C4m.encoded_squares_equal

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
import Theorems.Thm_Couret_InterIA_C4m_entries_distinct
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

theorem encoded_squares_equal (m : ℕ) (hm : 2 ≤ m) :
    encode (T m) ^ 2 = encode (U m) ^ 2 := by sorry















end Couret.InterIA.C4m
