-- Prove2me | solution 1 for Couret.InterIA.Fibres.cyclic_four_fixed_probes
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:40.164914+00:00
-- url     : https://prove2.me/submissions/e5ff4f1a-859d-4db2-92b1-129ff96b630c

import Definitions.Def_Couret_FixedMembershipProbes_e6019f9e3a1b
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Fibres_cyclic_four_fibre_ncard
import Theorems.Thm_Couret_InterIA_Fibres_xor_family_fixed_probes
import Definitions.Def_Couret_BinaryAffineFibre_5ba9c7ff8364
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity



























theorem p2m_local_cyclic_four_fixed_probes (n : ℕ) (hn : 0 < n)
    (S : Finset (ZMod n)) (hS : S.card=4) :
    ∃ d : ℕ, d ≤ 2 ∧ (cyclicFourFibre n S).ncard=2^d ∧
      ∃ q : Fin d → ZMod n, ProbeSeparates (cyclicFourFibre n S) q :=
  xor_family_fixed_probes _ (cyclic_four_fibre_ncard n hn S hS)
    (cyclic_four_fibre_xor_closed n hn S hS)

end Couret.InterIA.Fibres

theorem solution : ∀ (n : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀ (S : Finset.{0} (ZMod n)),
      @Eq.{1} Nat (@Finset.card.{0} (ZMod n) S) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        @Exists.{1} Nat fun d =>
          And (@LE.le.{0} Nat instLENat d (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (And
              (@Eq.{1} Nat (@Set.ncard.{0} (Finset.{0} (ZMod n)) (Couret.InterIA.Fibres.cyclicFourFibre n S))
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d))
              (@Exists.{1} (Fin d → ZMod n) fun q =>
                @Couret.InterIA.Fibres.ProbeSeparates.{0} (ZMod n) (ZMod.decidableEq n) d
                  (Couret.InterIA.Fibres.cyclicFourFibre n S) q)) := @_root_.Couret.InterIA.Fibres.p2m_local_cyclic_four_fixed_probes

