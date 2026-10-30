-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_Polya_NecklacePhi
-- name    : AnalyticCombinatorics_Ch1_Polya_NecklacePhi
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-24T23:51:06.335082+00:00
-- url     : https://prove2.me/theorems/1ca890ec-7fda-4444-af66-fe6ba7def18e
-- title:
--   Finite cyclic orbit spaces for necklaces
-- statement:
--   For a nonzero natural number $n$, the binary colorings $\mathbb Z/n\mathbb Z\to\{0,1\}$ are considered modulo cyclic translations of their positions. This foundation supplies the finite orbit-quotient structure for those colorings, using the translation action already defined in the enumeration foundation. It does not define a numerical necklace count by a prescribed gcd or totient formula.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/Polya/NecklacePhi.lean
--   Source code license: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_Polya_Enumeration
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Binary necklaces, totient form

This file converts the gcd-form Burnside sum for binary necklaces into the
classical Euler-totient form.
-/

namespace AnalyticCombinatorics.Ch1.Polya.NecklacePhi

open scoped BigOperators

attribute [local instance] arrowAction

noncomputable local instance orbitRelDecidableRel {G X : Type*} [Group G] [MulAction G X] :
    DecidableRel (MulAction.orbitRel G X).r :=
  Classical.decRel _

noncomputable local instance orbitQuotientFintype (n : ℕ) [NeZero n] :
    Fintype
      (MulAction.orbitRel.Quotient (Multiplicative (ZMod n)) (ZMod n → Bool)) :=
  Quotient.fintype (MulAction.orbitRel (Multiplicative (ZMod n)) (ZMod n → Bool))

end AnalyticCombinatorics.Ch1.Polya.NecklacePhi


