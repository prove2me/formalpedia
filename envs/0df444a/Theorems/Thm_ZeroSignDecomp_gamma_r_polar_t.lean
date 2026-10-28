-- Prove2me | Theorems.Thm_ZeroSignDecomp_gamma_r_polar_t
-- name    : ZeroSignDecomp.gamma_r_polar_t
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:27:06.213225+00:00
-- url     : https://prove2.me/theorems/1ae99f2c-0387-4c04-ab77-4b9ed44be840
-- title:
--   Phase of the real gamma factor on the critical line
-- statement:
--   Let $t\ne0$ and $\lambda$ be real and suppose
--
--   $$\Gamma\!\left(\frac14+\frac{it}{2}\right)
--   =\left|\Gamma\!\left(\frac14+\frac{it}{2}\right)\right|e^{i\lambda}.$$
--
--   For $\Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2)$, there is a real $M>0$ such that
--
--   $$\Gamma_{\mathbb R}(1/2+it)=M\,e^{i(\lambda-(t/2)\log\pi)}.$$
--
--   This identifies the phase in the completed-zeta sign argument.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/ZeroSignDecomp_t14.lean#L73-L112

import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_XiLineZeros
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
namespace ThetaGap
end ThetaGap
namespace XiLineZeros
end XiLineZeros
/-  ZeroSignDecomp_t14.lean -- ANDÚRIL G2-FULL: the phase-decomposition sign bridge that removes
    the Γℝ-VALUE (magnitude) blocker permanently, and the conditional first-zero theorem it enables.

    ## THE BLOCKER THIS FILE DISSOLVES.

    Every prior G2 rung (`CheckBand`, `FullyReflectedBand_t14`) carried the on-line `gLine` sign as a
    `memR`-membership HYPOTHESIS `gLine tᵢ ∈ boxᵢ` -- a VALUE enclosure.  Closing that in-kernel needs
    the Γℝ VALUE `Γℝ(1/2+it) = π^{-1/4-it/2}·Γ(1/4+it/2)`, whose MAGNITUDE `|Γℝ|` has no kernel
    enclosure anywhere in the corpus (repeatedly flagged: `FullyReflectedBand_t14` header gap (B),
    `ZeroHypBand_t14` header gap (B), `CheckBand` "the single precisely identified blocker").  A `gLine`
    VALUE box is therefore genuinely out of reach.

    But the IVT (`SignChain.exists_zero_of_sign_change`, `XiLineZeros`) consumes only the SIGN of
    `gLine`, never its value.  And the sign does NOT need the magnitude:

        gLine t = Re Λ(1/2+it) = Re(Γℝ(1/2+it)·ζ(1/2+it)),   Λ = Γℝ·ζ  (Mathlib
                  `riemannZeta_def_of_ne_zero`),
        Γℝ(1/2+it) = M·exp(iφ),  M = π^{-1/4}·‖Γ(1/4+it/2)‖ > 0,  φ = Λ_θ − (t/2)·log π,

    where `Λ_θ` is the branch-correct argument of `Γ(1/4+it/2)` DELIVERED, hypothesis-free, by the
    discharged `ThetaConverge.convergence_obligation` (`Γ = ‖Γ‖·exp(I·Λ_θ)`).  Since `M > 0`:

        gLine t = M·( cos φ · Re ζ(1/2+it)  −  sin φ · Im ζ(1/2+it) ),           (★)

    so `sign(gLine t) = sign( cos φ · Re ζ − sin φ · Im ζ )` -- the magnitude `M` cancels out of the
    sign.  `φ` is exactly the `ThetaConverge.theta_14_box` quantity (`−(t/2)log π + Λ_θ` = the
    Riemann–Siegel θ).  Numerically (driver): φ(14) ≈ −1.78295, and the sign quantity is `−0.1056` at
    `t=14`, `+0.7199` at `t=15` -- comfortable, kernel-boxable margins straddling a zero (γ₁ ≈ 14.1347).

    ## WHAT IS PROVED HERE (all axiom-clean: {propext, Classical.choice, Quot.sound}).

      * `gamma_r_polar_t` : the polar form `Γℝ(1/2+it) = M·exp(iφ)`, `M > 0`, `φ = Λ − (t/2)log π`,
        from the ThetaConverge branch identity and the `π^{-s/2}` cpow split.  GENERAL in `t ≠ 0`.
      * `gLine_sign_decomp_t` : identity (★), GENERAL in `t ≠ 0`, with `Λ` supplied INTERNALLY by
        `convergence_obligation` (no branch hypothesis leaks out) -- the crown lemma.
      * `exists_zero_of_sign_change` : the IVT single-pair bridge (inlined from `SignChain`, needing
        only `XiLineZeros`, so this file does not pull in the unbuilt `TuringBand` dependency).
      * `first_zero_of_sign_quantities` : **THE CONDITIONAL FIRST-ZERO THEOREM.**  Given the two
        sign-quantity facts (`cos φ₁₄·Re ζ₁₄ − sin φ₁₄·Im ζ₁₄ < 0` and the `> 0` analogue at `t=15`,
        with `φ` the θ-limits this file exposes), there is a zero of `completedRiemannZeta` in
        `(14, 15)`.  The Γℝ-magnitude blocker is GONE; the ONLY residual is the two sign quantities.

    ## THE PRECISE RESIDUAL (what still separates this from an argument-free `first_zero_kernel`).

    The hypotheses of `first_zero_of_sign_quantities` are exactly the kernel signs of
    `cos φ·Re ζ − sin φ·Im ζ` at `t ∈ {14, 15}`.  Discharging them in-kernel is PURE EMITTER
    THROUGHPUT, no further mathematics:
      (i)  `cos φ`, `sin φ` boxes -- from a tightened `ThetaConverge.theta_14_box` (the driver's
           honest-`k`≤30 + rational-harmonic-tail + cubic-bracket recipe, width ≈ 9.4e-4 < 2e-3);
           mechanical `ArctanTaylor.arctan_bracket` iteration, orthogonal to the analytic content.
      (ii) `Re ζ`, `Im ζ` boxes -- from the EM finite part `EMZetaTail.emZetaFinite3` (tail
           `em_zeta_critical_line3_number ≤ 1/1000`, PROVED) reduced via `EMZetaComplex.em_cpow_partial`
           + `integral_cpow` to the elementary Dirichlet sum `Σ_{n=1}^{199} n^{-s}` (each term boxed by
           `ZeroHypBand_t14.term_re`/`term_im` + a `TrigReduceOperating`-style `cos/sin(t·log n)` climb).
           The trig climb per term is the ~700-Int-op cost; ~199 terms × 2 grid points is the mission's
           ~2·10⁶-Int-op budget, and needs ~390 emitted operating-point certs (only 4 exist today:
           `cos/sin_14log2`, `cos/sin_14log200`).  A driver, not a theorem.

    conjecture1_proved = False.  The magnitude-free sign bridge + a conditional IVT zero theorem, NOT a
    proof of RH and NOT (yet) an argument-free zero-existence theorem.
-/





open Complex Real XiLineZeros ThetaGap

section
namespace ZeroSignDecomp
end ZeroSignDecomp
open ZeroSignDecomp

/-! ## 1.  The polar form of the Γℝ factor: `Γℝ(1/2+it) = M·exp(iφ)`, `M > 0`. -/

theorem ZeroSignDecomp.gamma_r_polar_t (t : ℝ) (ht : t ≠ 0) (Λ : ℝ)
    (hbranch : Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)
        = (‖Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)‖ : ℂ) * Complex.exp (Complex.I * (Λ:ℂ))) :
    ∃ M : ℝ, 0 < M ∧
      Gammaℝ ((1/2:ℂ) + (t:ℂ)*I)
        = (M:ℂ) * Complex.exp (Complex.I * ((Λ - (t/2) * Real.log Real.pi : ℝ):ℂ)) := by sorry
