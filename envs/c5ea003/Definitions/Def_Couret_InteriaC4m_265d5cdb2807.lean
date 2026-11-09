-- Prove2me | Definitions.Def_Couret_InteriaC4m_265d5cdb2807
-- name    : Couret_InteriaC4m_265d5cdb2807
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:54.29854+00:00
-- url     : https://prove2.me/theorems/c226276c-6547-4988-9475-cf2dec4b634b
-- title:
--   Two cyclic patterns and their group-ring encoding
-- statement:
--   Defines $T_m=\{0,1,m,2m+1\}$ and $U_m=\{0,m,m+1,3m+1\}$ in $\mathbb Z/(4m)\mathbb Z$. Also defines the integral group-ring indicator of a finite support as the sum of its point masses. The definitions are meaningful for every natural $m$; later theorems supply any positivity or distinctness assumptions.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/InteriaC4m.lean; source file SHA-256 20922ec6a91e45da3f1620e9daf510fabaf675a094c698e2eb771ab1c3cc3c6c

import Aesop
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









def T (m : ℕ) : Finset (ZMod (4*m)) := {0, 1, (m : ZMod (4*m)), ((2*m+1 : ℕ) : ZMod (4*m))}
def U (m : ℕ) : Finset (ZMod (4*m)) := {0, (m : ZMod (4*m)), ((m+1 : ℕ) : ZMod (4*m)), ((3*m+1 : ℕ) : ZMod (4*m))}





variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def encode (S : Finset G) : AddMonoidAlgebra ℤ G := ∑ a ∈ S, AddMonoidAlgebra.single a 1






















end Couret.InterIA.C4m


