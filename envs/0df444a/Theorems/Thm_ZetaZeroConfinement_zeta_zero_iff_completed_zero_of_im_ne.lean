-- Prove2me | Theorems.Thm_ZetaZeroConfinement_zeta_zero_iff_completed_zero_of_im_ne
-- name    : ZetaZeroConfinement.zeta_zero_iff_completed_zero_of_im_ne
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:59:55.737063+00:00
-- url     : https://prove2.me/theorems/26b56eda-5175-47b9-99c6-9eb719243f32
-- title:
--   Zeta and completed-zeta zeros off the real axis
-- statement:
--   For $\rho\in\mathbb C$ with $\operatorname{Im}\rho\ne0$,
--   $$\zeta(\rho)=0\quad\Longleftrightarrow\quad\Lambda(\rho)=0,$$
--   where $\Lambda$ is the completed Riemann zeta function. The gamma factor has no
--   zero at such a point.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_zero_localization/lean/ZetaZeroConfinement.lean#L40-L58

import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
/- CONFINEMENT (kernel): every nontrivial zeta zero up to height T lies in the band [a, 1-a].

   This is the "confinement" half of the "all zeros up to height T are on the line" project:
   box-localization (all zeros IN a box on the line, PR #312) + confinement (all zeros ARE in the
   box, this file).  We prove the confinement:

     `zero_in_band` :  a nontrivial zero `ρ` (`ζ ρ = 0`, `0 < ρ.im ≤ T`) with `a ≤ dlvpRateC/log T`
                       satisfies  `a ≤ ρ.re ≤ 1 - a`.

   Both edges come from the SELF-CONTAINED effective de la Vallée Poussin zero-free region
   `ZeroFreeBridge.riemannZeta_ne_zero_region` (PR #318 -- no multiplicity input, β≥3/4 discharged
   internally): `ζ(β+iγ) ≠ 0` for `|γ| ≥ 55/16` and `β > 1 - dlvpRateC/log|γ|`.

   - RIGHT edge `ρ.re ≤ 1-a`:  contrapositive of the region at `ρ` gives `ρ.re ≤ 1 - dlvpRateC/log|γ|`,
     and `dlvpRateC/log|γ| ≥ dlvpRateC/log T ≥ a` (log monotone, `|γ| = ρ.im ≤ T`; `dlvpRateC > 0`).
   - LEFT edge `a ≤ ρ.re`:  reflect through the functional equation.  `ζ ρ = 0` ⟹ `Λ ρ = 0`
     (unconditional strip bridge: `ρ.im ≠ 0` ⟹ `Gammaℝ ρ ≠ 0`) ⟹ `Λ (1-ρ) = 0`
     (`completedRiemannZeta_one_sub`) ⟹ `ζ (1-ρ) = 0` (strip bridge again, `(1-ρ).im = -ρ.im ≠ 0`).
     The reflected zero has real part `1-ρ.re`, height `-ρ.im`, `|-ρ.im| = |ρ.im| ≥ 55/16`.  The
     region contrapositive on it gives `1-ρ.re ≤ 1 - dlvpRateC/log|γ| ≤ 1 - a`, i.e. `ρ.re ≥ a`.

   RESIDUAL (documented, honest -- a genuine Mathlib gap, NOT a fake).  Mathlib has no "no zeta
   zeros with `|Im| < 14`" fact (the first nontrivial zero is at height ~14.13 > 55/16 ~ 3.44), so
   the region's height-floor hypothesis `55/16 ≤ |ρ.im|` is carried as an ADDED hypothesis `hγ` on
   `zero_in_band`.  It is a small classical fact, discharged at the concrete T=100 instantiation
   from the on-line sweep (all 29 zeros up to 100 have height ≥ 14 > 55/16).  No multiplicity input,
   no `β ≥ 3/4` casework, no `0 < ρ.re` strip hypothesis (the FE strip bridge here is unconditional
   for `ρ.im ≠ 0`).

   conjecture1_proved = False (a kernel-verified reduction of confinement to the effective dVP
   region + the functional equation, NOT a proof of RH).
-/



open Complex

section
namespace ZetaZeroConfinement
end ZetaZeroConfinement
open ZetaZeroConfinement

theorem ZetaZeroConfinement.zeta_zero_iff_completed_zero_of_im_ne {ρ : ℂ} (him : ρ.im ≠ 0) :
    riemannZeta ρ = 0 ↔ completedRiemannZeta ρ = 0 := by sorry
