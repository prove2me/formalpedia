-- Prove2me | Theorems.Thm_mme_schonhage_degenerates
-- name    : mme_schonhage_degenerates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-28T20:38:48.532096+00:00
-- url     : https://prove2.me/theorems/0a2fbfbc-3bf0-4857-8bb9-b0657c9c16a5
-- statement:
--   **Schönhage's explicit degeneration.** The direct sum $\langle4,1,4\rangle\oplus\langle1,9,1\rangle$ degenerates from the diagonal unit $I_{17}$ at order $2$ — i.e. it has border rank $\le 17 = 4\cdot4+1$. Witnessed by explicit polynomial vectors indexed by $(\mathrm{Fin}\,4\times\mathrm{Fin}\,4)\oplus\mathrm{Unit}$ with a correction term making the degree-0 and degree-1 coefficients vanish and the degree-2 coefficient the direct-sum tensor.
-- source:
--   https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_mme_degeneration
import Definitions.Def_mme_tensor_rank
universe u
open MME

theorem mme_schonhage_degenerates {K : Type u} [Field K] :
    DegeneratesOfOrder (TensorObj.bigAdd ![MMObj K 4 1 4, MMObj K 1 9 1])
      (TensorObj.diagObj K 3 17) 2 := by sorry
