-- Prove2me | solution 1 for Shamir1979.extension_consistency
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:02:41.874411+00:00
-- url     : https://prove2.me/submissions/3051f02e-8d21-411f-865b-8ee68cfe772c

import Mathlib
import Definitions.Def_Shamir1979_Model
open scoped BigOperators
universe u
open Shamir1979

theorem solution (p n m k : Nat) [Fact (Nat.Prime p)]
    (hk : 0 < k) (hkn : k ≤ n) (hnm : n ≤ m) (hmp : m < p)
    (secret : ZMod p) (coins : Coins p k) (i : Fin n) :
    share (n := m) secret coins (i.castLE hnm) = share (n := n) secret coins i := by
  rfl
