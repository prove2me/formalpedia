-- Prove2me | solution 1 for Heisenberg125.Heis.asum_perm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:20:56.269286+00:00
-- url     : https://prove2.me/submissions/104b6ed6-51d2-4829-8c61-d3c7a7b3f630

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} {L M : List (Heis p)} (h : L.Perm M) : asum L = asum M := by
  simp only [asum]
  exact (h.map Heis.a).sum_eq
