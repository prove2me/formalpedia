-- Prove2me | Theorems.Thm_gpy_combinedLcm_pos
-- name    : gpy_combinedLcm_pos
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T01:08:45.374951+00:00
-- url     : https://prove2.me/theorems/682a2f7e-89f3-40b3-ab35-f7e15aa1a409
-- title:
--   Positivity of the combined modulus on the support
-- statement:
--   For support pairs $(d,e)$ at any level $R$, the combined modulus $L(d,e)$, the lcm over coordinates of the coordinatewise lcms, is positive. Hence both $1/L$ and $1/\varphi(L)$ are genuine reals, with no division by zero in the comparison between the first-moment coefficient and the singular sum. Formalization Note: support membership is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY first-moment comparison, formalized from Mathlib (compatible pairs, good pairs, and the singular sum)

import Mathlib
open Classical

theorem gpy_combinedLcm_pos {k : ℕ} {R : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R))
    (he : e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R)) :
    0 < Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) := by sorry
