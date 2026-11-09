-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_short_bank_collision_dichotomy
-- name    : Couret.STROBO2TORS.recoh_short_bank_collision_dichotomy
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:56:20.011719+00:00
-- url     : https://prove2.me/theorems/e2168108-a6ea-423a-85aa-accd0cf38ce0
-- title:
--   A short mixed bank has a translation or reflected collision
-- statement:
--   Let $G$ be an abelian group and $R$ a commutative ring. Let finite abelian groups $H,V$ embed additively and injectively into $G$, with $2H=0$, $3V=0$ and $|V|=3^s$. Let $r>0$, $k<r+s$, and functions $f_i:G\to R$ for $i<k$ satisfy $f_i(x+y)=f_i(x)f_i(y)$ and $f_i(0)=1$. Supply additive $b_i:H\to\mathbb Z/2\mathbb Z$ and $c_i:V\to\mathbb Z/3\mathbb Z$ such that on embedded $H$, $f_i=1$ when $b_i=0$ and $f_i=-1$ otherwise; on embedded $V$, $c_i=0$ implies $f_i=1$. Assume that injectivity of the full binary map implies existence of $r$ distinct selected indices whose binary map onto $(\mathbb Z/2\mathbb Z)^r$ is surjective. For every triple $S=\{x,y,z\}$, one of the following collisions exists:
--
--   1. A nonzero $d$ with $2d=0$ such that $S\ne S+d$, their ordered squares agree, and all $k$ probe sums agree.
--   2. Nonzero $d,v$ with $2d=0$, $3v=0$ such that $A=\{0,v,v+d\}$ and $B=\{0,-v,-v+d\}$ are distinct, their ordered squares agree, and all $k$ probe sums agree.
--
--   $$\text{Translation collision}\quad\lor\quad\text{Reflected collision}.$$
--
--   No assumption $|H|=2^r$ is made directly; the stated information-set contract supplies the needed rank property.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohBinaryDichotomy.lean, lines 97–157; source file SHA-256 740733aa832d9a2d29988c8cbc79b0861bfba8e7e0e0aa8e9f9826db98ef1779; theorem Couret.STROBO2TORS.recoh_short_bank_collision_dichotomy

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_binary_bank_kernel_or_injective
import Theorems.Thm_Couret_STROBO2TORS_recoh_binary_kernel_genuine_collision
import Theorems.Thm_Couret_STROBO2TORS_recoh_pivot_bank_has_genuine_collision
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

theorem recoh_short_bank_collision_dichotomy
    {H V R : Type*}
    [AddCommGroup H] [Fintype H]
    [AddCommGroup V] [Fintype V]
    [CommRing R]
    (r s k : ℕ) (hr : 0 < r) (hk : k < r + s)
    (hcardV : Fintype.card V = 3 ^ s)
    (h2 : ∀ a : H, a + a = 0)
    (h3 : ∀ a : V, (a + a) + a = 0)
    (embH : H →+ G) (injH : Function.Injective embH)
    (embV : V →+ G) (injV : Function.Injective embV)
    (bank : Fin k → G → R)
    (hadd : ∀ i : Fin k, ∀ a b : G,
      bank i (a + b) = bank i a * bank i b)
    (hval0 : ∀ i : Fin k, bank i 0 = 1)
    (binary : Fin k → H →+ ZMod 2)
    (hbinary0 : ∀ i : Fin k, ∀ a : H,
      binary i a = 0 → bank i (embH a) = 1)
    (hbinary1 : ∀ i : Fin k, ∀ a : H,
      binary i a ≠ 0 → bank i (embH a) = -1)
    (ternary : Fin k → V →+ ZMod 3)
    (hternary : ∀ i : Fin k, ∀ a : V,
      ternary i a = 0 → bank i (embV a) = 1)
    (hinfo : Function.Injective
        (fun a : H => fun i : Fin k => binary i a) →
      ∃ pivot : Fin r → Fin k,
        Function.Injective pivot ∧
        Function.Surjective
          (fun a : H => fun j : Fin r => binary (pivot j) a))
    (x y z : G) (hcard : ({x, y, z} : Finset G).card = 3) :
    (∃ d : G, d ≠ 0 ∧ d + d = 0 ∧
      ({x, y, z} : Finset G) ≠ {x + d, y + d, z + d} ∧
      (∀ q : G,
        orderedSquare ({x, y, z} : Finset G) q =
          orderedSquare ({x + d, y + d, z + d} : Finset G) q) ∧
      (∀ i : Fin k,
        recohTripleProbe (bank i) x y z =
          recohTripleProbe (bank i) (x + d) (y + d) (z + d))) ∨
    (∃ d v : G, d ≠ 0 ∧ d + d = 0 ∧
      v ≠ 0 ∧ (v + v) + v = 0 ∧
      ({0, v, v + d} : Finset G) ≠ {0, -v, -v + d} ∧
      (∀ q : G,
        orderedSquare ({0, v, v + d} : Finset G) q =
          orderedSquare ({0, -v, -v + d} : Finset G) q) ∧
      (∀ i : Fin k,
        recohTripleProbe (bank i) 0 v (v + d) =
          recohTripleProbe (bank i) 0 (-v) (-v + d))) := by sorry


end Couret.STROBO2TORS
