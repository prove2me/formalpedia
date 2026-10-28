-- Prove2me | Theorems.Thm_ZetaReflection_em_saw_step_window_cpow
-- name    : ZetaReflection.em_saw_step_window_cpow
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:56:45.583305+00:00
-- url     : https://prove2.me/theorems/e2dff3d0-49fa-4e74-bc6b-3a4184a44497
-- title:
--   Euler–Maclaurin sawtooth step over a finite window
-- statement:
--   Let $k\ge1$, $M\le N$ be natural numbers, and let $f'=f_1$ on $[M,N]$, with
--   $f_1$ interval-integrable on every unit interval in the window. Let $b_k$ be the
--   periodic Bernoulli sawtooth and $B_{k+1}$ the Bernoulli function. Then
--   $$\int_M^N b_k(x)f(x)\,dx
--   =\frac{B_{k+1}(0)(f(N)-f(M))}{k+1}
--   -\frac1{k+1}\int_M^N b_{k+1}(x)f_1(x)\,dx.$$
--   This is the summed order-raising identity for a complex-valued integrand.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaTail.lean#L758-L854

import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Theorems.Thm_ZetaReflection_em_saw_step_cpow
/-  EMZetaTail.lean -- A2 Theorem 1, TAIL track: the order-K Euler-Maclaurin tail engine.

    The blocker of PROGRAM ANDÚRIL's reflection track.  Builds on `EMZeta.lean` /
    `EMZetaComplex.lean` (the K=1 chain).  The K=1 remainder envelope `‖s‖/(2·Re s)` proven in
    `EMZetaComplex.em_zeta_strip_enclosure` is sign-LOOSE (≈14 at s=1/2+14i), so the G2 reflected
    band could not be made sign-tight from it.  This file raises the Euler-Maclaurin order and cuts
    the sum at a finite `N`, producing a remainder that DECAYS like `N^{-Re s - K + 1}`, small enough
    to make `gLine` boxes sign-tight.

    Architecture (bottom-up), ALL kernel-clean (AxiomGuardEMTail):

      F.  Order-2/3 periodized "saw" Bernoulli sup bounds: `|sawBernoulli 2| ≤ 1/6`,
          `|sawBernoulli 3| ≤ 1/12` (via `B₃ = y(1−y)(1/2−y)`), and `bernoulliFun_three` closed form.
      G.  `em_saw_step` — the one IBP step raising the saw order by one over a unit cell (the proven
          form of `EMZetaWip.em_saw_step_wip`), via the continuous polynomial surrogate
          `B_{k+1}(x−m)/(k+1)`.  Endpoint saw values `B_{k+1}(0)`, `B_{k+1}(1)` (equal for `k+1≠1`).
      G'. `em_saw_step_window` — sum `em_saw_step` over `[M,N]`; interior boundary terms telescope
          (`bernoulliFun_endpoints_eq_of_ne_one`), leaving only `B_{k+1}(0)(fk N − fk M)/(k+1)`.
      H.  `em_tail_integral_bound` — the reusable engine: `‖∫_N^∞ saw_k · c·x^{−s−k}‖`
          ≤ `B·‖c‖·N^{−(Re s+k−1)}/(Re s+k−1)`, the `N`-decay that makes gLine boxes sign-tight.
      I.  `em_tail3_bound` (order-3, `B = 1/12`) and `em_tail3_number` — THE NUMBER: at the G2 pilot
          `s = 1/2 + 14i`, `N = 200`, the order-3 remainder is `≤ 10⁻³` (kernel-decided).  Clears the
          go/no-go the K=1 envelope `‖s‖/(2·Re s) ≈ 14` failed.

    REMAINING for the full ζ-order-K identity (handoff): tie `em_saw_step_window` to `riemannZeta` by
    raising the K=1 remainder `∫_1^∞ saw₁·(−s x^{−s−1})` (from `EMZetaComplex.em_zeta_strip`) to
    order 3 over `[N,∞)` — apply `em_saw_step_window` on `[N,M]` (complex cpow orders 2,3, derivative
    coefficients `s(s+1)…`), then `M → ∞` (boundary terms → 0; integral → `∫_N^∞`), reusing the
    `intervalIntegral_tendsto_integral_Ioi` limit pattern from `em_zeta_cpow`.  The remainder BOUND at
    the endpoint is already `em_tail3_bound`; only the identity plumbing remains.

    conjecture1_proved = False.  This is a classical analysis lemma (Euler-Maclaurin tail bound),
    NOT a proof of RH.
-/



open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real

section
namespace ZetaReflection
end ZetaReflection
open ZetaReflection

/-! ## F. Order-k periodized Bernoulli: derivative tower and explicit sup bounds. -/









/-! ## G. The saw-order-raising IBP step over a unit cell.

    The antiderivative tower: `sawBernoulli (k+1) / (k+1)` has derivative `sawBernoulli k` on the
    OPEN cell `(m, m+1)` (from `antideriv_bernoulliFun`, since `Int.fract` has derivative `1` off
    ℤ and `bernoulliFun (k+1)/(k+1)` has derivative `bernoulliFun k`).  IBP with this antiderivative
    turns `∫ sawBernoulli k · fk` into a boundary term plus `∫ sawBernoulli (k+1) · fk'`, exactly
    one order higher.  The endpoint saw values are `bernoulliFun (k+1) 0` and `bernoulliFun (k+1) 1`
    (the cell is `[m, m+1]`), which for `k+1 ≠ 1` are EQUAL by `bernoulliFun_endpoints_eq_of_ne_one`
    — the mechanism that makes the interior Bernoulli boundary terms telescope to zero. -/















/-! ## G'. Summed saw-order-raising over an integer window `[M, N]`.

    Summing `em_saw_step` over the cells `[M,M+1], …, [N-1,N]` and telescoping via
    `sum_integral_adjacent_intervals_Ico`, the interior boundary terms cancel (for `k+1 ≠ 1` the
    saw endpoint values `B_{k+1}(0) = B_{k+1}(1)` agree, so adjacent cells contribute
    `+B_{k+1}(0)·f(j)` and `−B_{k+1}(0)·f(j)`), leaving only the two outer endpoints:
        ∫_M^N saw_k · fk
          = B_{k+1}(0)·(fk N − fk M)/(k+1)  −  (∫_M^N saw_{k+1} · fk1)/(k+1).
    (Here `k ≥ 1` so `k + 1 ≠ 1`, which is what makes the telescoping clean.) -/



/-! ## H. The order-K tail remainder integrals and their explicit `N`-decaying bounds.

    The consumer needs a remainder over the TAIL `[N, ∞)` whose norm decays in `N`.  We work with
    the complex integrand `sawBernoulli k x · (c · (x:ℂ)^(-s-k))` where `c` is the falling-factorial
    coefficient `(-1)^k s(s+1)…(s+k-1)` (the k-th derivative coefficient of `x^{-s}`).  The norm
    bound is the clean product form
        ‖∫_N^∞ saw_k · c·x^{-s-k}‖ ≤ Bsup_k · ‖c‖ · N^{-Re s - k + 1} / (Re s + k - 1),
    from `‖saw_k‖ ≤ Bsup_k`, `‖x^{-s-k}‖ = x^{-Re s - k}`, and `∫_N^∞ x^{-Re s -k} = N^{-Re s -k+1}/(Re s+k-1)`. -/



/-! ## H'. The SHIFTED-BASE tail engine `(w + x)^{-a}` (the Binet / Γℝ substrate).

    The base-1 engine `em_tail_integral_bound` bounds saw-weighted `x^{-s-k}` tails.  The Binet
    remainder `μ_K(w)` (Stirling series for `ψ`) is, up to the finite Bernoulli peel, an
    Euler–Maclaurin tail of the trigamma power series `Σ (w+n)^{-2-k}` — a SHIFTED-BASE `(w+x)^{-a}`
    tail.  This subsection generalizes the engine to that base.  Crucially the exponent is kept REAL
    (`a : ℝ`, `a > 1`) — which is exactly the form the trigamma tail needs (`a = 2 + k ∈ ℕ`) — so
    the norm is `‖(w+x)^{-a}‖ = ‖w+x‖^{-a}` (`Complex.norm_cpow_real`, no `exp(arg·im)` factor), and
    the honest `N`-decay is driven by the base lower bound `‖w+x‖ ≥ Re(w+x) = Re w + x ≥ Re w + N`. -/





/-! ## I. The K = 3 instance and THE NUMBER (the go/no-go for full reflection).

    The order-3 tail remainder integrand is `sawBernoulli 3 x · (c₃(s) · x^{-s-3})` where
    `c₃(s) = -s(s+1)(s+2)` is the coefficient of `x^{-s-3}` in `d³/dx³(x^{-s})`.  `em_tail_integral_bound`
    bounds this integral for ANY complex `c`; here we record it with the honest falling-factorial
    coefficient and the proven saw-3 sup bound `1/12`, then evaluate the numeric envelope at the G2
    pilot point `s = 1/2 + 14i` and certify a tail cut making it `< 10⁻³` (the K = 1 envelope
    `‖s‖/(2·Re s) ≈ 14` did NOT — see EMZetaComplex.em_zeta_strip_enclosure). -/









/-! ## J. The order-2 windowed EM identity for the ζ integrand (complex).

    We raise the K=1 windowed complex EM identity (`euler_maclaurin_one_window_cpow` applied to
    `f x = (x:ℂ)^(-s)`) to order 2 using `em_saw_step_window` (real coefficients, applied to the
    real and imaginary parts — but here directly to the ℂ integrand via linearity of the identity
    over the real saw).  The order-2 remainder integrand carries the coefficient `c₂(s) = s(s+1)`.

    We give the complex σ-direction derivatives to order 2 (the inputs `em_saw_step_window` needs),
    then the windowed order-2 identity.  This is the reusable step; iterating once more gives order 3,
    and the `[N,∞)` limit (handoff) yields the ζ representation. -/



/-! ### ℂ-valued saw-order-raising over a window (for the ζ integrand).

    The ℂ lift of `em_saw_step` and `em_saw_step_window`.  The saw factor `sawBernoulli k x` stays
    REAL (cast to ℂ); `fk, fk1` are ℂ-valued.  Proof structure is identical to the real versions
    with `linear_combination` in place of `linarith` for the final ℂ arithmetic. -/

theorem ZetaReflection.em_saw_step_window_cpow {k : ℕ} (hk : 1 ≤ k) (M N : ℕ) (hMN : M ≤ N) (fk fk1 : ℝ → ℂ)
    (hd : ∀ x ∈ Icc (M : ℝ) N, HasDerivAt fk (fk1 x) x)
    (hi : ∀ j ∈ Finset.Ico M N, IntervalIntegrable fk1 volume (j : ℝ) (j + 1)) :
    (∫ x in (M : ℝ)..N, (sawBernoulli k x : ℂ) * fk x)
      = (bernoulliFun (k + 1) 0 : ℂ) * (fk N - fk M) / (k + 1)
        - (∫ x in (M : ℝ)..N, (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1) := by sorry
