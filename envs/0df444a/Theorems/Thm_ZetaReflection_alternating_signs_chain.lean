-- Prove2me | Theorems.Thm_ZetaReflection_alternating_signs_chain
-- name    : ZetaReflection.alternating_signs_chain
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:56:35.850077+00:00
-- url     : https://prove2.me/theorems/7a0fcb12-9efb-445d-9aca-7d665ac7ebcd
-- title:
--   Zeros from an alternating-sign sample chain
-- statement:
--   Let $p_0<\cdots<p_n$ lie in $[T_0,T_1]$, and suppose consecutive values of the
--   defined real function $g_{\rm line}$ have strictly opposite signs:
--   $$g_{\rm line}(p_i)g_{\rm line}(p_{i+1})<0\qquad(0\le i<n).$$
--   Then there is a strictly increasing list of $n$ heights $t$ in $[T_0,T_1]$ for
--   which
--   $$\Lambda_\zeta(1/2+it)=0.$$
--   Here $\Lambda_\zeta$ is the completed Riemann zeta function. The list provides
--   distinct critical-line zeros for the counting argument.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/SignChain.lean#L69-L124

import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Mathlib
import Theorems.Thm_ZetaReflection_exists_zero_of_sign_change
namespace XiLineZeros
end XiLineZeros
namespace ZetaZeroLocalization
end ZetaZeroLocalization
/-  SignChain.lean -- A2 Theorem 7: the alternating-sign-chain → hLine lemma.

    Generalizes the per-instance IVT pattern of `XiLineZeros` (lambda_zero_*, lambda_two_zeros_*,
    lambda_five_zeros_*) into ONE lemma parameterized by an arbitrary grid of `n+1` points:

        alternating_signs_chain

    Given `n+1` strictly increasing grid points `p₀ < p₁ < … < pₙ` in `[T0, T1]` at which the
    real critical-line function `gLine` takes strictly sign-alternating values (encoded as the
    single per-interval condition `gLine pᵢ · gLine pᵢ₊₁ < 0`), it produces the VERBATIM T5
    `hLine` shape (see `TuringBand.BandStatement`):

        ∃ xs : List ℝ, xs.length = n ∧ xs.IsChain (· < ·) ∧
          (∀ t ∈ xs, T0 ≤ t ∧ t ≤ T1) ∧
          (∀ t ∈ xs, completedRiemannZeta (1/2 + t·I) = 0)

    Each of the `n` consecutive sign-change subintervals yields, by the intermediate value
    theorem on the continuous `gLine`, one interior zero; strict monotonicity of the grid
    orders the zeros into a `<`-chain.  A reflected sign-sweep (kernel-checked rational bounds
    on `gLine` at the grid points, of alternating sign) discharges `hLine` through this lemma.

    conjecture1_proved = False.
-/



open Complex ZetaZeroLocalization XiLineZeros

section
namespace ZetaReflection
end ZetaReflection
open ZetaReflection

theorem ZetaReflection.alternating_signs_chain
    (T0 T1 : ℝ) (n : ℕ) (p : Fin (n + 1) → ℝ)
    (hmono : StrictMono p)
    (hlo : T0 ≤ p 0) (hhi : p (Fin.last n) ≤ T1)
    (hsign : ∀ i : Fin n, gLine (p i.castSucc) * gLine (p i.succ) < 0) :
    ∃ xs : List ℝ, xs.length = n ∧ xs.IsChain (· < ·) ∧
      (∀ t ∈ xs, T0 ≤ t ∧ t ≤ T1) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := by sorry
