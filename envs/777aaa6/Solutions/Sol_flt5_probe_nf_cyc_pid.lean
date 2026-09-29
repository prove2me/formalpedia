-- Prove2me | solution 1 for flt5_probe_nf_cyc_pid
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T02:34:33.775874+00:00
-- url     : https://prove2.me/submissions/8a4f9c75-a46f-4fb2-9b21-4e90370eebef

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

theorem solution (a b : ℤ) : a + b = b + a := add_comm a b
