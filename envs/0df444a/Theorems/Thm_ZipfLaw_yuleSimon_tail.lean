-- Prove2me | Theorems.Thm_ZipfLaw_yuleSimon_tail
-- name    : ZipfLaw.yuleSimon_tail
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:58.141217+00:00
-- url     : https://prove2.me/theorems/2765d49b-7d9c-4669-a8fa-ff678ed2e2c1
-- title:
--   Yule–Simon tail: $f(k;\rho)\sim C/k^{\rho+1}$
-- statement:
--   For every $\rho>0$ there is a constant $C>0$ such that the Yule–Simon frequencies $f(k;\rho)=\rho\,B(k,\rho+1)$ satisfy
--   $$f(k;\rho)\sim\frac{C}{k^{\rho+1}}\qquad(k\to\infty),$$
--   i.e. $f(k;\rho)\,k^{\rho+1}/C\to1$.
-- source:
--   Wikipedia, "Zipf's law" (https://en.wikipedia.org/wiki/Zipf%27s_law), snapshot uploaded by the proposer, section "Related laws" ("The tail frequencies of the Yule–Simon distribution are approximately f(k;ρ) ≈ [constant]/k^(ρ+1) for any choice of ρ > 0").

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem yuleSimon_tail (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧
      Asymptotics.IsEquivalent Filter.atTop (fun k : ℕ => yuleSimonPMF ρ k)
        (fun k : ℕ => C / (k : ℝ) ^ (ρ + 1)) := by sorry

end ZipfLaw
