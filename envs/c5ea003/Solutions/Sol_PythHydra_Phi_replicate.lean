-- Prove2me | solution 1 for PythHydra.Phi_replicate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:47:29.6958+00:00
-- url     : https://prove2.me/submissions/447f9b21-b40d-4190-a070-ca343a83a736

import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_HydraGame
open PythHydra in
theorem solution (k n m : ℕ) : Phi k (Multiset.replicate n m) = n * phi k m := by
  simp [Phi, Multiset.map_replicate, Multiset.sum_replicate, smul_eq_mul]
