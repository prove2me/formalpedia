-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_effective_spectral_convergence
-- name    : ZigZagStrong.ZigZag.effective_spectral_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:13.332448+00:00
-- url     : https://prove2.me/theorems/59bebeff-112c-4e29-922e-532c064b23b0
-- title:
--   Proposition 3.10 (corrected: nonnegative logarithmic factor)
-- statement:
--   There is an absolute positive constant $C$ such that for every $r\ge2$, every $c$-regular gadget $H$ on $d=2r$ vertices, all $n$ and all $\varepsilon>0$,
--   $$\Pr[\lambda_{\rm new}\ge\|A_{G_\lambda z H}\|+\varepsilon]\le C\frac dn\left(\frac{dc^2\log(d/2)}{\varepsilon}\right)^8\max\!\left(0,\log\frac{edc^2}{\varepsilon}\right).$$
--   For each fixed $H$, the same probability is bounded by $C_H/(n\varepsilon^9)$ with $C_H>0$ uniform over both $n$ and $\varepsilon$. Neither vertex transitivity nor goodness is required. This is the quantitative input to the main result.
--
--   Differences from the source:
--   - correction: The factor log(e*d*c^2/epsilon) for every epsilon>0 → max(0,log(e*d*c^2/epsilon)) for every epsilon>0; reason: For H=C6, d=6, c=2, r=3, n=2 and epsilon=48*e, the probability is zero but the printed right side is a positive prefactor times log(1/2)<0. Clipping only this factor preserves the positive-log estimate and the all-epsilon O conclusion.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Proposition 3.10, p. 13.

import Definitions.Def_ZigZagStrong_ZigZag_Covers

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem effective_spectral_convergence  : ∃ C : ℝ, 0 < C ∧
  ∀ r c : ℕ, 2 ≤ r → ∀ H : Gadget (2*r) c,
    (∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      StrongConv.uniformProb (fun σ : Fin r → Equiv.Perm (Fin n) =>
        ‖permutationLimit H‖ + ε ≤ ‖permutationNew H σ‖) ≤
        C * ((2*r : ℝ) / n) * ((2*r : ℝ) * (c : ℝ)^2 * Real.log r / ε)^8 *
          max 0 (Real.log (Real.exp 1 * (2*r : ℝ) * (c : ℝ)^2 / ε))) ∧
    (∃ C_H : ℝ, 0 < C_H ∧ ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      StrongConv.uniformProb (fun σ : Fin r → Equiv.Perm (Fin n) =>
        ‖permutationLimit H‖ + ε ≤ ‖permutationNew H σ‖) ≤ C_H / ((n : ℝ) * ε^9)) := by sorry

end ZigZagStrong.ZigZag
