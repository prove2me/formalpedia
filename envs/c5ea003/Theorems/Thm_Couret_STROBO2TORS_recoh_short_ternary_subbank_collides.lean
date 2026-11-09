-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_short_ternary_subbank_collides
-- name    : Couret.STROBO2TORS.recoh_short_ternary_subbank_collides
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:57:16.023793+00:00
-- url     : https://prove2.me/theorems/bee8fcd0-fa93-46a9-9a52-a99fd39edef7
-- title:
--   A short ternary subbank leaves an invisible reflection
-- statement:
--   Let $G$ be an abelian group. Let $A$ be a finite exponent-three abelian group of size $3^s$ embedded additively and injectively in $G$. Fix $d\ne0$ with $2d=0$. Let $f_i:G\to R$ ($i<k$) be multiplicative under addition with $f_i(0)=1$, for a commutative ring $R$. Choose $t<s$ indexed bank entries, allowing repeated indices. Suppose every bank entry either has $f_i(d)=-1$ or is one of the selected entries. Suppose additive $b_j:A\to\mathbb F_3$ satisfy $b_j(a)=0\Rightarrow f_{\mathrm{selected}(j)}(\operatorname{emb}(a))=1$. Then
--
--   $$\exists v\ne0,\ 3v=0:\quad S=\{0,v,v+d\}\ne T=\{0,-v,-v+d\},\quad Q_S=Q_T,\quad\sum_{a\in(0,v,v+d)}f_i(a)=\sum_{a\in(0,-v,-v+d)}f_i(a)\ (i<k).$$
--
--   This witnesses a reflection invisible to the entire bank.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohKernelCollisions.lean, lines 73–131; source file SHA-256 e531d83ad9b2feb52dc9ec79d690ceed0416e241f5f923161f3dcaf4db7e67e7; theorem Couret.STROBO2TORS.recoh_short_ternary_subbank_collides

import Aesop
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_short_ternary_bank_has_kernel
import Theorems.Thm_Couret_STROBO2TORS_recoh_three_torsion_probe_equal_iff_trivial
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b

set_option autoImplicit false

/-!
RECOH: bridge from rank-kernel witnesses to actual triple collisions.

This file contains only conditional lower-bound interfaces.
It does not assert the unrestricted sharp bound r+s, nor
the existence of the requisite spanning H-restrictions.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_short_ternary_subbank_collides
    {A R : Type*} [AddCommGroup A] [Fintype A] [CommRing R]
    (s t k : ℕ) (hcard : Fintype.card A = 3 ^ s) (ht : t < s)
    (h3 : ∀ a : A, (a + a) + a = 0)
    (emb : A →+ G) (hemb : Function.Injective emb)
    (d : G) (hd0 : d ≠ 0) (hd2 : d + d = 0)
    (bank : Fin k → G → R)
    (hadd : ∀ i : Fin k, ∀ x y : G,
      bank i (x + y) = bank i x * bank i y)
    (hzero : ∀ i : Fin k, bank i 0 = 1)
    (selected : Fin t → Fin k)
    (hcover : ∀ i : Fin k,
      bank i d = -1 ∨ ∃ j : Fin t, i = selected j)
    (bits : Fin t → A →+ ZMod 3)
    (hcompat : ∀ j : Fin t, ∀ a : A,
      bits j a = 0 → bank (selected j) (emb a) = 1) :
    ∃ v : G, v ≠ 0 ∧ (v + v) + v = 0 ∧
      ({0, v, v + d} : Finset G) ≠ {0, -v, -v + d} ∧
      (∀ q : G,
        orderedSquare ({0, v, v + d} : Finset G) q =
          orderedSquare ({0, -v, -v + d} : Finset G) q) ∧
      (∀ i : Fin k,
        recohTripleProbe (bank i) 0 v (v + d) =
          recohTripleProbe (bank i) 0 (-v) (-v + d)) := by sorry


end Couret.STROBO2TORS
