-- Prove2me | Theorems.Thm_KeplerMission_nonlinear_8055810915_valid
-- name    : KeplerMission.nonlinear_8055810915_valid
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-28T00:52:08.099986+00:00
-- url     : https://prove2.me/theorems/3fd2ae4f-bb97-4271-aa36-277c857abe47
-- title:
--   WAZLDCD 8055810915 — spherical disk nonoverlap inequality
-- statement:
--   Let $x=(x_1,\ldots,x_6)$ satisfy
--   $$4\le x_1\le (63/25)^2,\qquad x_2=4,\qquad x_3=(2h_0)^2,\qquad x_4=x_5=x_6=1,\qquad h_0=63/50.$$
--   The WAZLDCD nonlinear disk-nonoverlap inequality is
--   $$\operatorname{acs\_sqrt\_x1\_d4}(x)-\frac{\pi}{6}+\frac{797}{1000}
--   <\operatorname{arclength\_x\_123}(x).$$
--   Here $p=\mathrm{problem309}$ is the exact source record and $n=6$ is its arity. The function on the left is $\arccos(\operatorname{holSqrt}(x_1)/4)$; the right side is the source `arclength` applied to the signed square roots of $x_1,x_2,x_3$. All functions use the exact published definitions, including the source `atn2` branches and totalized division. The five fixed coordinates are retained in the formal statement, and the conclusion is strict at every endpoint.
--
--   **Formalization note.** This is a direct source inequality, source ID `8055810915`, represented by `Nonlinear.problem309.Valid`. It is the only record in the five-member packing-separation family not already in the four principal nonlinear families. Together with those family theorems it supplies the complete catalog; no certificate-completion or geometric-realizability hypothesis is added.
--
--   **Source.** Hales et al., A Formal Proof of the Kepler Conjecture (2017), https://doi.org/10.1017/fmp.2017.1; Section 5, PDF p. 12, equation (2), and PDF pp. 13–15; Section 6, PDF pp. 16–17. Formal source nonlinear/ineq.hl:1634–1648, source ID 8055810915 (WAZLDCD, disk nonoverlap), revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53; https://github.com/flyspeck/flyspeck/blob/1ce0353008eba83d3c76ae9a25c3c242e4802d53/text_formalization/nonlinear/ineq.hl#L1634-L1648. Family selector packing/YSSKQOY.hl:24–31; https://github.com/flyspeck/flyspeck/blob/1ce0353008eba83d3c76ae9a25c3c242e4802d53/text_formalization/packing/YSSKQOY.hl#L24-L31. This named source record has no separately numbered paper equation.
-- source:
--   Hales et al., A Formal Proof of the Kepler Conjecture (2017), https://doi.org/10.1017/fmp.2017.1; Section 5, PDF p. 12, equation (2), and PDF pp. 13–15; Section 6, PDF pp. 16–17. Formal source nonlinear/ineq.hl:1634–1648, source ID 8055810915 (WAZLDCD, disk nonoverlap), revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53; https://github.com/flyspeck/flyspeck/blob/1ce0353008eba83d3c76ae9a25c3c242e4802d53/text_formalization/nonlinear/ineq.hl#L1634-L1648. Family selector packing/YSSKQOY.hl:24–31; https://github.com/flyspeck/flyspeck/blob/1ce0353008eba83d3c76ae9a25c3c242e4802d53/text_formalization/packing/YSSKQOY.hl#L24-L31. This named source record has no separately numbered paper equation.

import Definitions.Def_Kepler_NonlinearCatalogModel
set_option autoImplicit false

namespace KeplerMission
theorem nonlinear_8055810915_valid : Nonlinear.problem309.Valid := by sorry
end KeplerMission
