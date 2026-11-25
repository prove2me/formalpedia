-- Prove2me | Theorems.Thm_collatz_late_mergers_after_first_odd_run_residue_classes
-- name    : collatz_late_mergers_after_first_odd_run_residue_classes
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T20:50:44.542502+00:00
-- url     : https://prove2.me/theorems/8ab80a1f-2453-5a45-a958-361a3ddf7b36
-- title:
--   Late Collatz mergers in 25 progressions after the first odd-run exit
-- statement:
--   Let $C$ be the ordinary Collatz map. Take any natural number $n$ in one of the following congruence classes.
--
--   | Modulus | Residues |
--   | --- | --- |
--   | $1224440064$ | $524071407$ |
--   | $11019960576$ | $2338056687$, $2957834991$, $3862823151$, $6016620015$, $6497574639$, $6918369519$, $7647666159$, $8278858479$, $8544237807$, $8578203375$, $9083530735$, $10717660911$, $10768609263$ |
--   | $22039921152$ | $15112762095$ |
--   | $99179645184$ | $57926895$, $236993263$, $818377455$, $2643882991$, $3611896815$, $4273203183$, $4278013167$, $5557880559$, $5635018479$, $5765693679$ |
--
--   For $r=v_2(n+1)$ and $W=3^r(n+1)/2^r-1$, the first odd-run exit occurs at clock $2r+v_2(W)$. Prove that this clock is $9$ and that
--   $$
--   \exists k,a,b\in\mathbb N,\qquad 0<k<n,\qquad a\in\{13,15\},\qquad C^a(n)=C^b(k).
--   $$
--   The displayed merger clocks occur after the first run exits. Each row is a claim about the entire progression, with arbitrary nonnegative progression parameter.
-- source:
--   Auxiliary to https://prove2.me/theorems/cddb7ade-1644-4d22-a993-2e20ff00dde6. Both trajectories are checked as affine progressions, using the progression method in https://prove2.me/theorems/1843fe6d-cde2-4133-a4d5-fcfa32356e48.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorization.Basic

theorem collatz_late_mergers_after_first_odd_run_residue_classes (n : ℕ) (h : ∃ p : ℕ × ℕ, p∈([(1224440064, 524071407), (11019960576, 2338056687), (11019960576, 2957834991),
      (11019960576, 3862823151), (11019960576, 6016620015), (11019960576, 6497574639),
      (11019960576, 6918369519), (11019960576, 7647666159), (11019960576, 8278858479),
      (11019960576, 8544237807), (11019960576, 8578203375), (11019960576, 9083530735),
      (11019960576, 10717660911), (11019960576, 10768609263), (22039921152, 15112762095),
      (99179645184, 57926895), (99179645184, 236993263), (99179645184, 818377455),
      (99179645184, 2643882991), (99179645184, 3611896815), (99179645184, 4273203183),
      (99179645184, 4278013167), (99179645184, 5557880559), (99179645184, 5635018479),
      (99179645184, 5765693679)] : List (ℕ × ℕ)) ∧ n%p.1=p.2) :
    let r := (n+1).factorization 2
    let w := 3^r*((n+1)/2^r)-1
    w.factorization 2+2*r=9 ∧
      ∃ k a b : ℕ, 0<k ∧ k<n ∧ (a=13 ∨ a=15) ∧ collatzStep^[a] n=collatzStep^[b] k := by
  sorry
