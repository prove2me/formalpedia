-- Prove2me | Theorems.Thm_ZInQ_RouteK_Rank_certifiedRankTYZClRk
-- name    : ZInQ.RouteK.Rank.certifiedRankTYZClRk
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T20:09:44.506236+00:00
-- url     : https://prove2.me/theorems/3f7b6b11-5f38-468a-bb70-24871ca3f603
-- title:
--   CR$_3^{\mathrm{TYZ\_Cl,Rk}}$ — positive rank from the odd genus sum
-- statement:
--   The certified-rank hypothesis in its positive-rank, class-number form. For every squarefree natural number $d\equiv 5\pmod 8$ whose $(7,3)$ genus sum $T_{5b}(d)=\sum_{\pi}\prod_{B\in\pi}\#\bigl(2\mathrm{Cl}(\mathbb{Q}(\sqrt{-d_B}))\bigr)$ is odd (equal to $1$ in $\mathbb{Z}/2\mathbb{Z}$), the congruent number curve $C_d:y^2=x^3-d^2x$ has a rational point of infinite order. This is the form of CR$_3$ closest to Tian–Yuan–Zhang's own quantities; it implies every other form of CR$_3$ in the kernel. It rests on Tian–Yuan–Zhang's genus-period argument (with Proposition N) and Gross–Zagier with an auxiliary imaginary quadratic field.
-- source:
--   https://github.com/elliotglazer/diophantine-z-q/blob/964d7dd71f253091dbc5eac793b78cc56d1fcc73/ZInQKernel/RouteK/Rank/Statements.lean#L60-L72

import Mathlib
import Definitions.Def_ZInQLiterature

theorem ZInQ.RouteK.Rank.certifiedRankTYZClRk : ZInQ.RouteK.Rank.CertifiedRankTYZClRk := by sorry
