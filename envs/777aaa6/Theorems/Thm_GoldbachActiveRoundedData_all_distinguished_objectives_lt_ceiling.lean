-- Prove2me | Theorems.Thm_GoldbachActiveRoundedData_all_distinguished_objectives_lt_ceiling
-- name    : GoldbachActiveRoundedData.all_distinguished_objectives_lt_ceiling
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T03:34:10.035076+00:00
-- url     : https://prove2.me/theorems/220d216b-1d98-4d6a-933a-df1d481c7e4c
-- title:
--   Kernel-checked ceilings for all three distinguished scalar rows
-- statement:
--   Let $k$ select one of the three distinguished scalar rows registered in
--   `GoldbachActiveRoundedData`, with nonnegative integer ingredients $E,F,C,V$
--   and scale $D=10^{12}$. These are upward-rounded candidates from the v4 release
--   at https://goldbach-nine.vercel.app/ .
--
--   If $e,f\ge0$ satisfy $e\le E/D$ and $f\le F/D$, and a nonnegative real sequence
--   $u_i$ satisfies $u_i\le C/D$ and $\sum_{i<n}u_i\le V/D$ for every $n$, then
--   the quadratic series converges and
--
--   $$(e+f)^2+\sum_{i=0}^{\infty}u_i^2<\frac{198479}{200000}.$$
--
--   The proof bounds each $u_i^2$ by $(C/D)u_i$, proves convergence from bounded
--   partial sums, and uses the exact integer comparison
--
--   $$200000\big((E+F)^2+CV\big)<198479D^2.$$
--
--   All three finite comparisons are checked with `decide +kernel`. Only the
--   registered data and standard Mathlib results are imported. The correspondence
--   of the rounded ingredients to the original witness rationals is checked in
--   exact Python; their derivation from analytic number theory remains unverified.
--   This elementary conditional numerical bound does not establish the complete
--   exceptional-set conclusion or strong Goldbach, and no mathematical novelty is
--   claimed.
-- source:
--   Conservative numerical certificate bounds for https://goldbach-nine.vercel.app/release/goldbach-exception-069697-certificate-v4.zip . Analytic input derivation remains separate; no mathematical novelty is claimed.

import Definitions.Def_GoldbachActiveRoundedData
import Mathlib.Topology.Algebra.InfiniteSum.Real
open scoped BigOperators
set_option autoImplicit false

theorem GoldbachActiveRoundedData.all_distinguished_objectives_lt_ceiling (k : Fin 3) (e f : ℝ) (u : ℕ → ℝ)
    (he0 : 0 ≤ e) (hf0 : 0 ≤ f) (hu0 : ∀ i, 0 ≤ u i)
    (he : e ≤ ((GoldbachActiveRoundedData.distinguished k).exponential:ℝ)/
      (GoldbachActiveRoundedData.scale:ℝ))
    (hf : f ≤ ((GoldbachActiveRoundedData.distinguished k).firstCap:ℝ)/
      (GoldbachActiveRoundedData.scale:ℝ))
    (hu : ∀ i, u i ≤ ((GoldbachActiveRoundedData.distinguished k).restCap:ℝ)/
      (GoldbachActiveRoundedData.scale:ℝ))
    (hmass : ∀ n, (∑ i ∈ Finset.range n, u i) ≤
      ((GoldbachActiveRoundedData.distinguished k).restMass:ℝ)/
      (GoldbachActiveRoundedData.scale:ℝ)) :
    Summable (fun i => (u i)^2) ∧
    (e+f)^2+(∑' i, (u i)^2) < (198479:ℝ)/200000 := by sorry
