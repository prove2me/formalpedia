-- Prove2me | Theorems.Thm_ZipkinLostSales_Bounds_lemma_7
-- name    : ZipkinLostSales.Bounds.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:26:15.397993+00:00
-- url     : https://prove2.me/theorems/7cb4a862-abf0-4185-ae25-77e9e7efdb22
-- title:
--   Lemma 7, p. 940 — the last-period optimal cost f_T(v) is nondecreasing in v
-- statement:
--   Consider the lost-sales model of §4 under its standing assumptions. The optimal cost in the last period,
--   $$f_T(v)=\inf_{z\ge0} q(v,z),$$
--   is nondecreasing on the state space $V$ for the componentwise order: if $v,v'\in V$ and $v_l\le v'_l$ for every $l$, then $f_T(v)\le f_T(v')$.
--
--   Together with the convexity of $g_t$ in $z$, this is what propagates monotonicity backwards in Theorem 8.
--
--   **Formalization Note** $f_T$ is `fB M 1` (one period to go). The paper proves the lemma for $L=1$ and says the proof for larger $L$ is similar; the statement here is for every $L\ge1$. "Nondecreasing in $\mathbf v$" is monotonicity on $V$ for the pointwise order on $\mathbb R^L$. The minimum is an infimum over $z\ge0$; the identification with §2's model is not formalized.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 940 (PDF p. 5), Lemma 7

import Mathlib
import Definitions.Def_ZipkinLostSales_Bounds_Model

namespace ZipkinLostSales.Bounds

/-- Lemma 7, p. 940: the optimal cost `f_T(v)` (`fB M 1`) is nondecreasing in `v` on `V`, for the
componentwise order. -/
theorem lemma_7 {L : ℕ} (M : Data) (hM : Assumptions L M) :
    MonotoneOn (fB M 1) (ZipkinLostSales.LNatural.V L) := by sorry

end ZipkinLostSales.Bounds
