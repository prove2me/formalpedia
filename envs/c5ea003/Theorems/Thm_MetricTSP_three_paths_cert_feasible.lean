-- Prove2me | Theorems.Thm_MetricTSP_three_paths_cert_feasible
-- name    : MetricTSP.three_paths_cert_feasible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T20:12:25.916029+00:00
-- url     : https://prove2.me/theorems/453fb77d-078c-4c6c-a65f-cf32a19a7622
-- title:
--   The fractional certificate is feasible for the subtour LP
-- statement:
--   The classical fractional solution of the three-parallel-paths instance --- weight $1$ on internal path edges, $2/3$ on the six hub edges, and $1/6$ on the six pairs of equal-position cities adjacent to a hub --- is a feasible point of the subtour-elimination relaxation for $k \ge 2$:
--
--   1. it is symmetric, has zero diagonal, and takes values in $[0,1]$;
--   2. every city has fractional degree exactly $2$ (e.g. a city at position $1$ collects $2/3$ from its hub edge, $1$ from its path edge, and $2 \times 1/6$ from its two companions at position $1$);
--   3. every nontrivial cut is crossed with weight at least $2$. A cut separating the hubs crosses all three paths, each with weight at least $2/3$; a cut with both hubs on one side isolates part of some path and pays two crossings along it, the borderline cases (a path cut off at both its hub edges, $2/3 + 2/3$) being completed to $2$ exactly by the four $1/6$ pairs at its ends.
--
--   Together with the objective computation this certifies that the Held--Karp value of the instance is at most $3k+3$.
-- source:
--   M. X. Goemans, Worst-case comparison of valid inequalities for the TSP, Mathematical Programming 69 (1995) 335-349, Section 4 (the fractional solution of the three-path family); D. P. Williamson, D. B. Shmoys, The Design of Approximation Algorithms, CUP 2011, Figure 11.4 (the fractional solution pictured for the subtour LP).

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_three_paths

namespace MetricTSP

theorem three_paths_cert_feasible (k : ℕ) (hk : 2 ≤ k) : IsHeldKarp (tpCert k) := by sorry

end MetricTSP
