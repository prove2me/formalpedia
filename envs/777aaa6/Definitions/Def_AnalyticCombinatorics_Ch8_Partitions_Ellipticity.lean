-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_Ellipticity
-- name    : AnalyticCombinatorics_Ch8_Partitions_Ellipticity
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:17:21.691982+00:00
-- url     : https://prove2.me/theorems/a4f1f78d-cb3a-4cc9-95c1-639b5b7c8b39
-- title:
--   Ellipticity
-- statement:
--   The source mathematical objects and operations are specified by the following definitions.
--
--   ```lean
--   def edgeEnergyInt (L : ℕ) (f : ℤ → ℝ) : ℝ := ∑ r ∈ intEdges L, edgeSq f r
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/Ellipticity.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_DirichletForm
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Nearest-neighbor ellipticity lower bound (renewal route B, Layer-2 Stage 3c lower)

The lower half of the Dirichlet-form sandwich (ChatGPT ac2 R12 + R13): a `±1` minorization
(`Kc r (r+1) ≥ p`, `Kc (r+1) r ≥ p`) forces the directed jump energy to dominate the nearest-neighbor
edge energy,

  `2p · ∑_r (f(r+1) − f r)² ≤ ∑_{d,e} Kc(d,e)·(f e − f d)²`.

Each undirected edge `(r,r+1)` collects `≥ 2p` from its two directed nearest-neighbor jumps; the two
NN masks are extracted from the full double sum via collapsing inner indicator sums (`sum_eq_single`)
and `sum_filter`.  Combined with `DirichletForm.bounded_jump_energy_le_edge_energy` this gives the full
form sandwich `2p·E_edge ≤ E_K ≤ 3B²·E_edge`.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Nearest-neighbor edge energy on the integer interval. -/
def edgeEnergyInt (L : ℕ) (f : ℤ → ℝ) : ℝ := ∑ r ∈ intEdges L, edgeSq f r

end AnalyticCombinatorics.Ch8.Partitions.Erdos


