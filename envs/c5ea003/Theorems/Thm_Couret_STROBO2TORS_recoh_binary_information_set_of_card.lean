-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_binary_information_set_of_card
-- name    : Couret.STROBO2TORS.recoh_binary_information_set_of_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:55:57.910202+00:00
-- url     : https://prove2.me/theorems/38c8ea0b-efb3-420b-8b54-911c16192c10
-- title:
--   An injective binary bank contains an information set
-- statement:
--   Let $H$ be a finite abelian group of exponent two and size $2^r$. Let $b_0,\ldots,b_{k-1}:H\to\mathbb F_2$ be additive maps whose joint evaluation is injective. There is an injective index map $\pi:\{0,\ldots,r-1\}\to\{0,\ldots,k-1\}$ such that
--
--   $$a\longmapsto(b_{\pi(j)}(a))_{j<r}\text{ is surjective onto }\mathbb F_2^r.$$
--
--   Thus $r$ selected measurements provide full binary coordinates.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohBinaryLinearTransport.lean, lines 81–94; source file SHA-256 5cbb44f8ac5aad6f63d170a7fc63e533aac72967c7f079ea654d26b9087fc8a1; theorem Couret.STROBO2TORS.recoh_binary_information_set_of_card

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_binary_coordinates_of_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_binary_information_set_additive
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness

set_option autoImplicit false

/-!
RECOH: transport of binary additive characters to linear probes.
Research candidate. No global B(G) claim. The additive equivalence
assumption is essential: do not apply this to C2 × C4 as a whole.
-/

namespace Couret.STROBO2TORS

theorem recoh_binary_information_set_of_card
    {H : Type*} [AddCommGroup H] [Fintype H]
    (r k : ℕ) (h2 : ∀ a : H, a + a = 0)
    (hcardH : Fintype.card H = 2 ^ r)
    (binary : Fin k → H →+ ZMod 2)
    (hinj : Function.Injective
      (fun a : H => fun i : Fin k => binary i a)) :
    ∃ pivot : Fin r → Fin k,
      Function.Injective pivot ∧
      Function.Surjective
        (fun a : H => fun j : Fin r => binary (pivot j) a) := by sorry


end Couret.STROBO2TORS
