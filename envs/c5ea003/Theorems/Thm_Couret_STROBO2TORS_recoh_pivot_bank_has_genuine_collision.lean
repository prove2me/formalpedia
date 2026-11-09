-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_pivot_bank_has_genuine_collision
-- name    : Couret.STROBO2TORS.recoh_pivot_bank_has_genuine_collision
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:49:37.298089+00:00
-- url     : https://prove2.me/theorems/aa997431-7694-420f-84c0-a0482a905a35
-- title:
--   An undersized pivot bank has a genuine reflection collision
-- statement:
--   Let $G$ be an abelian group. Let finite abelian groups $H,V$ of exponents dividing two and three embed additively and injectively into $G$. Let $|V|=3^s$, $r>0$, $k<r+s$, and let $f_i:G\to R$ ($i<k$) be multiplicative under addition with $f_i(0)=1$, where $R$ is any commutative ring. Let $b_i:H\to\mathbb F_2$ be additive, and choose $r$ distinct pivot indices such that their joint binary evaluation onto $\mathbb F_2^r$ is surjective. Assume $b_i(a)\ne0$ implies $f_i(\operatorname{emb}_H(a))=-1$. Let $c_i:V\to\mathbb F_3$ be additive with $c_i(a)=0$ implying $f_i(\operatorname{emb}_V(a))=1$. Then
--
--   $$\exists\text{ a genuine reflected collision invisible to all }k\text{ probes}.$$
--
--   There exist $d,v\in G$ with $d\ne0$, $2d=0$, $v\ne0$ and $3v=0$ such that $S=\{0,v,v+d\}$ and $T=\{0,-v,-v+d\}$ are distinct, have equal ordered-square counts, and have equal sums of the three displayed character values for every bank entry. This supplies the mixed binary/ternary bank lower-bound witness.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohPivotCollision.lean, lines 18–127; source file SHA-256 257b958abd3db51c3274d1b72eeabb6d37611aa042b0fc101e79c88f3df7986d; theorem Couret.STROBO2TORS.recoh_pivot_bank_has_genuine_collision

import Aesop
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_order_three_reflection_same_square
import Theorems.Thm_Couret_STROBO2TORS_recoh_probe_reflection_of_cancel
import Theorems.Thm_Couret_STROBO2TORS_recoh_reflection_supports_distinct
import Theorems.Thm_Couret_STROBO2TORS_recoh_short_indexed_ternary_bank_has_kernel
import Theorems.Thm_Couret_STROBO2TORS_recoh_surjective_binary_pivots_leave_short_mask
import Theorems.Thm_Couret_STROBO2TORS_recoh_three_torsion_probe_equal_iff_trivial
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b

set_option autoImplicit false

/-!
RECOH: compose surjective binary pivots and indexed ternary kernels
to construct an actual indistinguishable pair of distinct three-point supports.

The hypotheses explicitly require compatible binary and ternary encodings
of the character restrictions. The unconditional existence of pivots for
an arbitrary full-rank bank remains a separate unproved obligation.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_pivot_bank_has_genuine_collision
    {H V R : Type*}
    [AddCommGroup H] [Fintype H]
    [AddCommGroup V] [Fintype V]
    [CommRing R]
    (r s k : ℕ)
    (hr : 0 < r)
    (hk : k < r + s)
    (hcardV : Fintype.card V = 3 ^ s)
    (h2 : ∀ a : H, a + a = 0)
    (h3 : ∀ a : V, (a + a) + a = 0)
    (embH : H →+ G) (injH : Function.Injective embH)
    (embV : V →+ G) (injV : Function.Injective embV)
    (bank : Fin k → G → R)
    (hadd : ∀ i : Fin k, ∀ x y : G,
      bank i (x + y) = bank i x * bank i y)
    (hzero : ∀ i : Fin k, bank i 0 = 1)
    (binary : Fin k → H →+ ZMod 2)
    (pivot : Fin r → Fin k)
    (hpiv : Function.Injective pivot)
    (hsurj : Function.Surjective
      (fun a : H => fun j : Fin r => binary (pivot j) a))
    (hbinary : ∀ i : Fin k, ∀ a : H,
      binary i a ≠ 0 → bank i (embH a) = -1)
    (ternary : Fin k → V →+ ZMod 3)
    (hternary : ∀ i : Fin k, ∀ a : V,
      ternary i a = 0 → bank i (embV a) = 1) :
    ∃ (d v : G),
      d ≠ 0 ∧ d + d = 0 ∧
      v ≠ 0 ∧ (v + v) + v = 0 ∧
      ({0, v, v + d} : Finset G) ≠ {0, -v, -v + d} ∧
      (∀ z : G,
        orderedSquare ({0, v, v + d} : Finset G) z =
          orderedSquare ({0, -v, -v + d} : Finset G) z) ∧
      (∀ i : Fin k,
        recohTripleProbe (bank i) 0 v (v + d) =
          recohTripleProbe (bank i) 0 (-v) (-v + d)) := by sorry


end Couret.STROBO2TORS
