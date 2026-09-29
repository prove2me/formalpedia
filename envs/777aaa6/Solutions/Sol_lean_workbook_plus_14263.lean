-- Prove2me | solution 1 for lean_workbook_plus_14263
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:47:05.769713+00:00
-- url     : https://prove2.me/submissions/be2fa323-99e2-4ec9-8c80-e00f634c43cd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {m n a b : ℕ} (hm : m ∣ n^a + 1) (hn : m ∣ n^b + 1) : m ∣ Nat.gcd (n^a + 1) (n^b + 1) := by
  intros
  exact Nat.dvd_gcd hm hn
