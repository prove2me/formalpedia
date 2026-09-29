-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR13.sourceOmega_monic
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:42:15.268+00:00
-- url     : https://prove2.me/submissions/eb36ed17-a683-4d4c-8a73-0d722035bc11

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBTopDegreeR13
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic

namespace PaperR11
end PaperR11

namespace PaperR12
end PaperR12

/-!
# Exact top degree of the literal cleared B numerator



The unique leading term is the unshifted pair (s,l)=(13*n,1).
This is a finite polynomial proof: neither A*F-B=H nor Omega divisibility
is an assumption. The canonical monic quotient V is defined even before
its remainder is known to vanish; its degree is not misrepresented as
proof that this remainder vanishes.
-/

namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12
open scoped BigOperators

lemma monic_finset_product {ι : Type*} (s : Finset ι) (p : ι → ℤ[X])
    (hp : ∀ i ∈ s, (p i).Monic) : (∏ i ∈ s, p i).Monic := by
  classical
  revert hp
  induction s using Finset.induction_on with
  | empty => intro hp; simp
  | @insert i s his ih =>
      intro hp
      rw [Finset.prod_insert his]
      exact (hp i (Finset.mem_insert_self i s)).mul
        (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))
end ErdosProblems.Erdos1049.PaperR13

open Polynomial PaperR11 PaperR12
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR13 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution (n : ℕ) : (sourceOmega n).Monic := by
  unfold sourceOmega
  exact monic_finset_product _ _
    (fun l _ => (cyclotomic.monic l ℤ).pow _)
