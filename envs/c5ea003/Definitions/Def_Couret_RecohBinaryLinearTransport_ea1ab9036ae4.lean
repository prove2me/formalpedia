-- Prove2me | Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
-- name    : Couret_RecohBinaryLinearTransport_ea1ab9036ae4
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:29.664529+00:00
-- url     : https://prove2.me/theorems/991b9a88-c4fe-4f0b-9f8f-6f5b970f5f72
-- title:
--   Binary characters as linear functionals
-- statement:
--   Converts additive maps to $\mathbb Z/2\mathbb Z$ into linear maps over that field. Given coordinates $H\cong(\mathbb Z/2\mathbb Z)^r$ and a bank of $k$ binary additive characters, transports each character to a dual linear functional on the coordinate space. This enables rank and information-set arguments.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohBinaryLinearTransport.lean; source file SHA-256 5cbb44f8ac5aad6f63d170a7fc63e533aac72967c7f079ea654d26b9087fc8a1

import Aesop
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

/-- Every additive map between F₂-vector spaces is F₂-linear. -/
def recoh_binary_character_linear
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : V →+ ZMod 2) : V →ₗ[ZMod 2] ZMod 2 :=
  f.toZModLinearMap 2

/-- Transport binary additive characters through a specified additive
equivalence to canonical coordinates. -/
def recoh_binary_bank_linear
    {H : Type*} [AddCommGroup H]
    (r k : ℕ)
    (e : H ≃+ (Fin r → ZMod 2))
    (binary : Fin k → H →+ ZMod 2) :
    Fin k → Module.Dual (ZMod 2) (Fin r → ZMod 2) :=
  fun i => recoh_binary_character_linear (binary i |>.comp e.symm.toAddMonoidHom)







end Couret.STROBO2TORS


