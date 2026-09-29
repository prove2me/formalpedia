-- Prove2me | Theorems.Thm_mme_degenerate_rank_le
-- name    : mme_degenerate_rank_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-28T20:42:36.049688+00:00
-- url     : https://prove2.me/theorems/1c8cea63-3f70-4490-b1a3-df8122239e2d
-- statement:
--   **Border rank bounds rank with polynomial overhead (Bini).** If `Z` degenerates from $I_R$ of order $H$, then $\mathrm{tensorRankObj}\,Z \le R\cdot(H+1)^d$: truncating the order-$H$ degeneration at $\varepsilon^{H+1}$ turns it into an honest restriction, contributing at most $(H+1)$ per tensor leg.
-- source:
--   https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf

import Definitions.Def_mme_degeneration
import Definitions.Def_mme_tensor_rank
open MME
universe u

theorem mme_degenerate_rank_le {K : Type u} [Field K] {d : ℕ}
    {Z : TensorObj K d} {R H : ℕ}
    (hdeg : DegeneratesOfOrder Z (TensorObj.diagObj K d R) H) :
    tensorRankObj Z ≤ R * (H + 1) ^ d := by sorry
