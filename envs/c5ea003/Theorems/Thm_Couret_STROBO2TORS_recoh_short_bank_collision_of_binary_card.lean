-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_short_bank_collision_of_binary_card
-- name    : Couret.STROBO2TORS.recoh_short_bank_collision_of_binary_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:02:54.289772+00:00
-- url     : https://prove2.me/theorems/d33ab45d-f250-4b9f-86f0-5399e0f9d80b
-- title:
--   Binary and ternary encodings force a short-bank collision
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $P_\chi(S)=\sum_{x\in S}\chi(x)$, and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S$ counts ordered sums and $B$ is a bank of complex additive characters. Let finite abelian groups $L,V$ have sizes $2^r,3^s$, with $2L=0$, $3V=0$, and injective additive embeddings into $G$. Let $R$ be any commutative ring and $f_i:G\to R$ for $i<k$ satisfy $f_i(a+b)=f_i(a)f_i(b)$ and $f_i(0)=1$. Assume $r>0$, $k<r+s$. Supply additive binary maps $b_i:L\to\mathbb F_2$ with $f_i(x)=1$ on embedded $b_i(x)=0$ and $f_i(x)=-1$ on embedded $b_i(x)\ne0$, and ternary maps $c_i:V\to\mathbb F_3$ with $f_i(x)=1$ whenever $c_i(x)=0$. For any three distinct $x,y,z\in G$, either a nonzero two-torsion translation of their support is different but has identical ordered square and all triple probes, or there exist nonzero $u\in G[2]$, $v\in G[3]$ for which the distinct supports $\{0,v,v+u\}$, $\{0,-v,-v+u\}$ share both data. $$\text{A translation collision or a reflection collision exists.}$$ No restriction on the characteristic of $R$ is added.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohBinaryStructuralDichotomy.lean, lines 15–62; source file SHA-256 dc6f50a8d341d5ccb0715f1e68f32f1090ae5d26497fe51241a74cd8529b077f; theorem Couret.STROBO2TORS.recoh_short_bank_collision_of_binary_card

import Aesop
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_binary_information_set_of_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_short_bank_collision_dichotomy
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4

set_option autoImplicit false

/-! Structural composition for elementary abelian binary torsion.
The general conditional theorem is preserved; this corollary discharges
its information-set obligation from exponent two and cardinality.
It does not establish the global optimal-bank formula.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_short_bank_collision_of_binary_card
    {H V R : Type*}
    [AddCommGroup H] [Fintype H]
    [AddCommGroup V] [Fintype V]
    [CommRing R]
    (r s k : ℕ) (hr : 0 < r) (hk : k < r + s)
    (hcardV : Fintype.card V = 3 ^ s)
    (hcardH : Fintype.card H = 2 ^ r)
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
