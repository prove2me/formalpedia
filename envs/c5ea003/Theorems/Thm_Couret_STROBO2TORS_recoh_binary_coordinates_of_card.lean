-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_binary_coordinates_of_card
-- name    : Couret.STROBO2TORS.recoh_binary_coordinates_of_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:48:57.877444+00:00
-- url     : https://prove2.me/theorems/731cfc15-df5e-4fd8-a429-1f2ed4569c6a
-- title:
--   Binary coordinates for a finite exponent-two group
-- statement:
--   Let $H$ be a finite abelian group with $2a=0$ for all $a\in H$ and $|H|=2^r$. Then
--
--   $$H\cong(\mathbb Z/2\mathbb Z)^r\quad\text{as additive groups}.$$
--
--   This supplies coordinates for its elementary two-torsion structure, including $r=0$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohBinaryLinearTransport.lean, lines 62–79; source file SHA-256 5cbb44f8ac5aad6f63d170a7fc63e533aac72967c7f079ea654d26b9087fc8a1; theorem Couret.STROBO2TORS.recoh_binary_coordinates_of_card

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

theorem recoh_binary_coordinates_of_card
    {H : Type*} [AddCommGroup H] [Fintype H]
    (r : ℕ) (h2 : ∀ a : H, a + a = 0)
    (hcardH : Fintype.card H = 2 ^ r) :
    Nonempty (H ≃+ (Fin r → ZMod 2)) := by sorry




end Couret.STROBO2TORS
