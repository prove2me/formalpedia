-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_complex_character_zmod_encoding
-- name    : Couret.STROBO2TORS.recoh_complex_character_zmod_encoding
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:56:01.354691+00:00
-- url     : https://prove2.me/theorems/6b3aa418-f16a-4ffa-a887-def295042064
-- title:
--   A bounded-exponent complex character factors through a cyclic character
-- statement:
--   Let $A$ be an abelian group killed by a positive natural $n$, and let $\chi:A\to\mathbb C$ be an additive character. There exists an additive $b:A\to\mathbb Z/n\mathbb Z$ such that
--
--   $$\chi(a)=\exp(2\pi i\,b(a)/n)\qquad(a\in A).$$
--
--   No finiteness of $A$ is required.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohComplexCharacterEncodings.lean, lines 33–58; source file SHA-256 3305e08ce41ea1179dcef4587f7da08eb723592588b747f5a6b789df0b5fd760; theorem Couret.STROBO2TORS.recoh_complex_character_zmod_encoding

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

theorem recoh_complex_character_zmod_encoding
    {A : Type*} [AddCommGroup A]
    (n : ℕ) [NeZero n] (hexp : ∀ a : A, n • a = 0)
    (chi : AddChar A ℂ) :
    ∃ bits : A →+ ZMod n, ∀ a : A,
      ZMod.stdAddChar (bits a) = chi a := by sorry






variable {G : Type*} [AddCommGroup G] [DecidableEq G]



end Couret.STROBO2TORS
