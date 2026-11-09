-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_short_complex_character_bank_collision
-- name    : Couret.STROBO2TORS.recoh_short_complex_character_bank_collision
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:17:19.614506+00:00
-- url     : https://prove2.me/theorems/4a768e5c-d75a-479d-9a79-07a5e46ffd6d
-- title:
--   A short complex bank has a translation or reflection collision
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $P_\chi(S)=\sum_{x\in S}\chi(x)$, and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S$ counts ordered sums and $B$ is a bank of complex additive characters. Let finite abelian groups $L,V$ have cardinalities $2^r,3^s$, respectively, with $2L=0$, $3V=0$, and injective additive embeddings into $G$. Assume $r>0$ and $k<r+s$. For any $k$ complex characters and any three distinct elements $x,y,z\in G$, at least one of the following exists: (1) a nonzero $u\in G[2]$ such that the support $\{x,y,z\}$ and its translate by $u$ are different but have the same ordered square and all $k$ triple probes; (2) nonzero $u\in G[2]$, $v\in G[3]$ such that $\{0,v,v+u\}$ and $\{0,-v,-v+u\}$ are different but have the same ordered square and all $k$ triple probes. $$\text{A translation collision or an exceptional reflection collision exists.}$$
--
--   The second alternative need not involve the supplied triple.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohComplexCharacterEncodings.lean, lines 100–146; source file SHA-256 3305e08ce41ea1179dcef4587f7da08eb723592588b747f5a6b789df0b5fd760; theorem Couret.STROBO2TORS.recoh_short_complex_character_bank_collision

import Aesop
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
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
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_complex_character_binary_encoding
import Theorems.Thm_Couret_STROBO2TORS_recoh_complex_character_zmod_encoding
import Theorems.Thm_Couret_STROBO2TORS_recoh_short_bank_collision_of_binary_card
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.Choose

set_option autoImplicit false

/-!
RECOH: character restrictions provide their own finite-field encodings.

Every complex additive character on a group annihilated by n factors
through the standard character of ZMod n. The binary and ternary
specializations discharge the compatibility assumptions of the existing
short-bank collision theorem. No primary character extension or upper
bound is assumed here.
-/

namespace Couret.STROBO2TORS









variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_short_complex_character_bank_collision
    {H V : Type*}
    [AddCommGroup H] [Fintype H]
    [AddCommGroup V] [Fintype V]
    (r s k : ℕ) (hr : 0 < r) (hk : k < r + s)
    (hcardV : Fintype.card V = 3 ^ s)
    (hcardH : Fintype.card H = 2 ^ r)
    (h2 : ∀ a : H, a + a = 0)
    (h3 : ∀ a : V, (a + a) + a = 0)
    (embH : H →+ G) (injH : Function.Injective embH)
    (embV : V →+ G) (injV : Function.Injective embV)
    (bank : Fin k → AddChar G ℂ)
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
