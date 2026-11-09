-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_short_binary_bank_collides
-- name    : Couret.STROBO2TORS.recoh_short_binary_bank_collides
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:56:54.414905+00:00
-- url     : https://prove2.me/theorems/9a6d657f-49ed-494a-b605-e7b1ddeb87dc
-- title:
--   A short binary bank misses a nontrivial triple translation
-- statement:
--   Let $G$ be an abelian group. Let $A$ be a finite exponent-two abelian group of size $2^r$ embedded additively and injectively in $G$. Let $k<r$ and let $f_i:G\to R$ ($i<k$), for a commutative ring $R$, satisfy $f_i(x+y)=f_i(x)f_i(y)$. Suppose additive binary maps $b_i:A\to\mathbb F_2$ satisfy $b_i(a)=0\Rightarrow f_i(\operatorname{emb}(a))=1$. For any $x,y,z\in G$ whose support $S=\{x,y,z\}$ has three elements,
--
--   $$\exists d\ne0:\quad 2d=0,\quad S\ne S+d,\quad Q_S=Q_{S+d},\quad\sum_{a\in(x,y,z)}f_i(a)=\sum_{a\in(x+d,y+d,z+d)}f_i(a)\ (i<k).$$
--
--   Thus the short bank cannot distinguish a nontrivial translation in any triple orbit.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohKernelCollisions.lean, lines 17–71; source file SHA-256 e531d83ad9b2feb52dc9ec79d690ceed0416e241f5f923161f3dcaf4db7e67e7; theorem Couret.STROBO2TORS.recoh_short_binary_bank_collides

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_short_binary_bank_has_kernel
import Theorems.Thm_Couret_STROBO2TORS_recoh_triple_probe_translate
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_free_of_card_three
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

theorem recoh_short_binary_bank_collides
    {A R : Type*} [AddCommGroup A] [Fintype A] [CommRing R]
    (r k : ℕ) (hcard : Fintype.card A = 2 ^ r) (hk : k < r)
    (h2 : ∀ a : A, a + a = 0)
    (emb : A →+ G) (hemb : Function.Injective emb)
    (bank : Fin k → G → R)
    (hadd : ∀ i : Fin k, ∀ x y : G,
      bank i (x + y) = bank i x * bank i y)
    (bits : Fin k → A →+ ZMod 2)
    (hcompat : ∀ i : Fin k, ∀ a : A,
      bits i a = 0 → bank i (emb a) = 1)
    (x y z : G)
    (ht : ({x, y, z} : Finset G).card = 3) :
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
