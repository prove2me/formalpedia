-- Prove2me | Definitions.Def_Bridges_ResidueLeakageLabNotes
-- name    : Bridges_ResidueLeakageLabNotes
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:38:28.669991+00:00
-- url     : https://prove2.me/theorems/bb74ce12-8beb-427a-878c-ac7aca680dcc
-- title:
--   Aether Catalog definitions — Bridges_ResidueLeakageLabNotes
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ResidueLeakageLabNotes`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ResidueLeakageLabNotes.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
/-
# Lab notes: machine-checked instances of the residue-leakage theorems

Companion to `Bridges.ResidueLeakageDirichletNoPruning` and
`Bridges.ResidueLeakagePatternSurjectivity`.  Everything below is *checked by
the kernel* through the `norm_num` extension for Jacobi symbols — no
`native_decide`, no appeal to an external computation.

Probe basis: the first `K = 5` primes `A₅ = [2,3,5,7,11]`, conductor
`4 · 2·3·5·7·11 = 9240`.

Target: `N₀ = 1591 = 37 · 43`, fingerprint `F(N₀) = [1,-1,1,-1,1]`.

* `qrLab_target` : the fingerprint of the target.
* `qrLab_periodicity` : `F(N₀ + 9240) = F(N₀)` — the conductor really is `9240`.
* `qrLab_compensators` : for each of the twelve candidate primes
  `13,17,…,59` an explicit compensating prime `q` with `F(p·q) = F(N₀)`;
  this is the finite shadow of `dirichlet_no_pruning`.
* `qrLab_all_32_patterns` : thirty-two explicit primes whose fingerprints are
  pairwise distinct, hence realise **all** `2^5 = 32` sign patterns; the finite
  shadow of `qrFingerprint_pattern_surjective`.
-/


namespace Bridges.ResidueLeakage.LabNotes

open Bridges.ResidueLeakage

/-- The first five primes. -/
def A₅ : List ℕ := [2, 3, 5, 7, 11]








/-- Thirty-two primes, one for each sign pattern. -/
def patternWitnesses : List ℕ :=
  [53, 17, 277, 181, 67, 311, 41, 107, 71, 79, 61, 113, 101, 271, 37, 59,
   197, 47, 211, 239, 103, 127, 167, 19, 23, 131, 97, 43, 13, 31, 29, 479]

/-- Their fingerprints. -/
def patternValues : List (List ℤ) :=
  [[-1, -1, -1, 1, 1], [1, -1, -1, -1, -1], [-1, 1, -1, 1, -1], [-1, 1, 1, -1, 1],
   [-1, -1, -1, -1, -1], [1, 1, 1, 1, -1], [1, -1, 1, -1, -1], [-1, 1, -1, -1, 1],
   [1, 1, 1, -1, -1], [1, -1, 1, -1, 1], [-1, 1, 1, -1, -1], [1, -1, -1, 1, 1],
   [-1, -1, 1, -1, -1], [1, -1, 1, 1, 1], [-1, 1, -1, 1, 1], [-1, 1, 1, 1, -1],
   [-1, -1, -1, 1, -1], [1, 1, -1, 1, -1], [-1, -1, 1, -1, 1], [1, 1, 1, -1, 1],
   [1, -1, -1, 1, -1], [1, -1, -1, -1, 1], [1, 1, -1, 1, 1], [-1, -1, 1, 1, 1],
   [1, 1, -1, -1, -1], [-1, 1, 1, 1, 1], [1, 1, -1, -1, 1], [-1, -1, -1, -1, 1],
   [-1, 1, -1, -1, -1], [1, -1, 1, 1, -1], [-1, -1, 1, 1, -1], [1, 1, 1, 1, 1]]





end Bridges.ResidueLeakage.LabNotes


