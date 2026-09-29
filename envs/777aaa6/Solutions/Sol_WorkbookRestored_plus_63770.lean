-- Prove2me | solution 1 for WorkbookRestored.plus_63770
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:02:41.994085+00:00
-- url     : https://prove2.me/submissions/10e9c21f-e95f-4c1f-8ebd-925d3e0458bf

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_63770.
  Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (p t : ℕ) (hp : p.Prime) (ht : t ≠ 0)
    : multiplicity p (choose (p^t) (p^(t-1))) = 1   := by
  apply multiplicity_eq_of_emultiplicity_eq_some
  rw [hp.emultiplicity_choose_prime_pow (Nat.pow_le_pow_right hp.pos (Nat.sub_le t 1)) (pow_ne_zero _ hp.ne_zero)]
  have hm : multiplicity p (p ^ (t - 1)) = t - 1 :=
    multiplicity_eq_of_emultiplicity_eq_some hp.emultiplicity_pow_self
  rw [hm]
  have ht1 : t - (t - 1) = 1 := by omega
  rw [ht1]
#print axioms solution
