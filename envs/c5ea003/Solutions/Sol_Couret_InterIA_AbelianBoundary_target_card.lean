-- Prove2me | solution 1 for Couret.InterIA.AbelianBoundary.target_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:04:49.649484+00:00
-- url     : https://prove2.me/submissions/67f60ac7-dd50-4617-9efa-55cbd90b6077

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




theorem p2m_local_target_card : T.card = 4 := by decide




end Couret.InterIA.AbelianBoundary

theorem solution : @Eq.{1} Nat (@Finset.card.{0} Couret.InterIA.AbelianBoundary.G4 Couret.InterIA.AbelianBoundary.T)
  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) := @_root_.Couret.InterIA.AbelianBoundary.p2m_local_target_card

