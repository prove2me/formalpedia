-- Prove2me | solution 1 for Heisenberg125.Heis.csum_perm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:29:53.041965+00:00
-- url     : https://prove2.me/submissions/8f8f93cc-5498-46f8-adc3-c84d54eee163

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} {L M : List (Heis p)} (h : L.Perm M) : csum L = csum M := by
  simp only [csum]
  exact (h.map Heis.c).sum_eq
