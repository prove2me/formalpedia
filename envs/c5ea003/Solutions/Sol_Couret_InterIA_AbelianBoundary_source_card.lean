-- Prove2me | solution 1 for Couret.InterIA.AbelianBoundary.source_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:04:40.305839+00:00
-- url     : https://prove2.me/submissions/6238cbee-b60c-486f-97cd-1bc3df56d72b

import Definitions.Def_Couret_AbelianBoundary_ad32094cf511
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret.InterIA.AbelianBoundary
open Finset Couret.InterIA.Parity



theorem p2m_local_source_card : S.card = 4 := by decide





end Couret.InterIA.AbelianBoundary

theorem solution : @Eq.{1} Nat (@Finset.card.{0} Couret.InterIA.AbelianBoundary.G4 Couret.InterIA.AbelianBoundary.S)
  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) := @_root_.Couret.InterIA.AbelianBoundary.p2m_local_source_card

