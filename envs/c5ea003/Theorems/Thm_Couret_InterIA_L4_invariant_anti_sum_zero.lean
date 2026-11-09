-- Prove2me | Theorems.Thm_Couret_InterIA_L4_invariant_anti_sum_zero
-- name    : Couret.InterIA.L4.invariant_anti_sum_zero
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:47.546707+00:00
-- url     : https://prove2.me/theorems/8a608474-da2e-4f19-bb63-01cdb5a527b6
-- title:
--   invariant anti sum zero
-- statement:
--   For every type α, every function τ:α→α, and all integer-valued functions f,g on α such that f(τ(x))=f(x), g(τ(x))=−g(x), and f(x)+g(x)=0 for every x∈α, both f and g are the zero function. No involution or bijectivity of τ is assumed; α may be empty.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-1-catalogue-equivalence-20261103/L4Foundations.lean, lines 142–155; source file SHA-256 a80b43da8931fa1cb12280548eeb0978b71553697ecec5546d5732de3fbdf552; theorem Couret.InterIA.L4.invariant_anti_sum_zero

import Definitions.Def_Couret_L4Foundations_a0fb4bb69682
import Mathlib.Data.Finset.Insert
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

set_option autoImplicit false

namespace Couret.InterIA.L4

section Cyclic







end Cyclic

section Rectangle
variable {G : Type*} [AddCommGroup G] [DecidableEq G]



end Rectangle



section Algebra
variable {R : Type*} [CommRing R]









end Algebra

section IntegerCoefficients
variable {α : Type*}

theorem invariant_anti_sum_zero (τ : α → α) (f g : α → ℤ)
    (hinv : ∀ x, f (τ x)=f x) (hanti : ∀ x, g (τ x)= -g x)
    (hsum : ∀ x, f x+g x=0) : f=0 ∧ g=0 := by sorry


end IntegerCoefficients

end Couret.InterIA.L4
