-- Prove2me | solution 1 for Heisenberg125.Heis.bsum_perm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:25:38.121626+00:00
-- url     : https://prove2.me/submissions/67b623c9-c9b6-4e10-a21e-444f1a0f5274

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} {L M : List (Heis p)} (h : L.Perm M) : bsum L = bsum M := by
  simp only [bsum]
  exact (h.map Heis.b).sum_eq
