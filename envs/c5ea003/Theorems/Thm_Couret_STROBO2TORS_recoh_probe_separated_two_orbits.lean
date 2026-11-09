-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_probe_separated_two_orbits
-- name    : Couret.STROBO2TORS.recoh_probe_separated_two_orbits
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:42:44.623771+00:00
-- url     : https://prove2.me/theorems/ace81a00-53a7-491b-8ffb-928cff770a85
-- title:
--   One orbit-constant character separates two internally separated orbits
-- statement:
--   Let G be an abelian group, S finite supports, chi complex additive characters, P_chi(S)=sum_(x in S)chi(x), and H={u:2u=0}. An H-orbit is {S+u:u in H}. A bank is delta-separated on a finite candidate family if every two distinct candidates have some coordinate whose probe difference has norm at least delta. Assume G finite. Let a bank B delta-separate both Orb_H(S) and Orb_H(T), for real delta. Let chi be a complex additive character trivial on H with $$\delta\le|P_\chi(S)-P_\chi(T)|.$$ Then adjoining one slot chi to B delta-separates the union of the two orbits. No disjointness, positive-delta or nonempty-bank premise is imposed.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohProbeStability.lean#L113-L141, lines 113–141; source file SHA-256 1d695a0d84e83ff92491e95ea472df8f9bf1059d52c5525c794d82c7f31a9800; theorem Couret.STROBO2TORS.recoh_probe_separated_two_orbits

import Aesop
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_probe_constant_on_torsion_orbit
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
Quantitative separation of character readings.  A separation statement uses
an existential coordinate; no finite maximum, nonempty bank, or nontrivial
fibre is silently assumed.  In particular singleton fibres and empty banks
are handled by the same definition.
-/

namespace Couret.STROBO2TORS



variable {G : Type*} [AddCommGroup G] [DecidableEq G]













variable [Fintype G]

theorem recoh_probe_separated_two_orbits
    {I : Type*} (bank : I → AddChar G ℂ) (chi : AddChar G ℂ)
    (S T : Finset G) (δ : ℝ)
    (hS : RecohProbeSeparated bank (torsionOrbit S) δ)
    (hT : RecohProbeSeparated bank (torsionOrbit T) δ)
    (htrivial : ∀ u : G, u + u = 0 → chi u = 1)
    (hcross : δ ≤ ‖recohSupportProbe chi S - recohSupportProbe chi T‖) :
    RecohProbeSeparated (Sum.elim bank (fun _ : Unit => chi))
      (torsionOrbit S ∪ torsionOrbit T) δ := by sorry












end Couret.STROBO2TORS
