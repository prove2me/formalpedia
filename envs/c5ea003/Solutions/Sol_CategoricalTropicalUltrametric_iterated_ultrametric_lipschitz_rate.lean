-- Prove2me | solution 1 for CategoricalTropicalUltrametric.iterated_ultrametric_lipschitz_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T00:02:48.717504+00:00
-- url     : https://prove2.me/submissions/1463e4f9-b4f4-4522-9375-15c1fdd704f0

import Mathlib
import Definitions.Def_Bridges_CategoricalTropicalUltrametric

open CategoricalTropicalUltrametric

theorem solution {X : TropicalValuationCarrier} {f : X.K → X.K} {C : ℕ}
    (hLip : ∀ x, (valuationReconstruct X).norm (f x)
      ≤ C * (valuationReconstruct X).norm x) :
    ∀ n x, (valuationReconstruct X).norm ((f^[n]) x)
      ≤ C ^ n * (valuationReconstruct X).norm x := by
  intro n x
  induction n with
  | zero => simp
  | succ n ih =>
    calc (valuationReconstruct X).norm ((f^[n + 1]) x)
        = (valuationReconstruct X).norm (f (f^[n] x)) := by
          rw [Function.iterate_succ_apply']
      _ ≤ C * (valuationReconstruct X).norm (f^[n] x) := hLip _
      _ ≤ C * (C ^ n * (valuationReconstruct X).norm x) :=
          Nat.mul_le_mul_left C ih
      _ = C ^ (n + 1) * (valuationReconstruct X).norm x := by ring
