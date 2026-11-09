-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_binary_kernel_genuine_collision
-- name    : Couret.STROBO2TORS.recoh_binary_kernel_genuine_collision
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:49:00.304791+00:00
-- url     : https://prove2.me/theorems/f78eec97-80c7-44b6-90b6-b4991b133404
-- title:
--   A binary common kernel produces a genuine invisible triple collision
-- statement:
--   Let $G,H$ be abelian groups, with $2H=0$, and let $e:H\hookrightarrow G$ be additive. Let $R$ be a commutative ring and $f_i:G\to R$ for $i<k$ satisfy $f_i(a+b)=f_i(a)f_i(b)$. Let $b_i:H\to\mathbb Z/2\mathbb Z$ be additive and assume $b_i(a)=0$ implies $f_i(e(a))=1$. If some nonzero $a\in H$ belongs to every $\ker b_i$, then for every triple $S=\{x,y,z\}$ of distinct points there exists $d\ne0$ with $2d=0$ such that
--
--   $$S\ne S+d,\qquad R_S=R_{S+d},\qquad\sum_{s\in S}f_i(s)=\sum_{s\in S+d}f_i(s)\quad(i<k).$$
--
--   The claim does not require finite ambient groups.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohBinaryDichotomy.lean, lines 41–95; source file SHA-256 740733aa832d9a2d29988c8cbc79b0861bfba8e7e0e0aa8e9f9826db98ef1779; theorem Couret.STROBO2TORS.recoh_binary_kernel_genuine_collision

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_triple_probe_translate
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_free_of_card_three
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b

set_option autoImplicit false

/-!
RECOH: binary evaluation dichotomy and exact collision reduction.

This module eliminates a manual case split for arbitrary finite banks:
either a nonzero binary kernel exists or the binary evaluation is injective.
In the injective case it records the information-set selection as one
EXPLICIT hypothesis. It does not claim that selection for general rank.

The rank-one case has a separate certified branch and is not duplicated.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_binary_kernel_genuine_collision
    {H R : Type*}
    [AddCommGroup H] [CommRing R]
    (k : ℕ)
    (h2 : ∀ a : H, a + a = 0)
    (embH : H →+ G) (injH : Function.Injective embH)
    (bank : Fin k → G → R)
    (hadd : ∀ i : Fin k, ∀ a b : G,
      bank i (a + b) = bank i a * bank i b)
    (binary : Fin k → H →+ ZMod 2)
    (hzero : ∀ i : Fin k, ∀ a : H,
      binary i a = 0 → bank i (embH a) = 1)
    (kernel : ∃ a : H, a ≠ 0 ∧ ∀ i : Fin k, binary i a = 0)
    (x y z : G) (hcard : ({x, y, z} : Finset G).card = 3) :
    ∃ d : G,
      d ≠ 0 ∧ d + d = 0 ∧
      ({x, y, z} : Finset G) ≠ {x + d, y + d, z + d} ∧
      (∀ q : G,
        orderedSquare ({x, y, z} : Finset G) q =
          orderedSquare ({x + d, y + d, z + d} : Finset G) q) ∧
      (∀ i : Fin k,
        recohTripleProbe (bank i) x y z =
          recohTripleProbe (bank i) (x + d) (y + d) (z + d)) := by sorry




end Couret.STROBO2TORS
