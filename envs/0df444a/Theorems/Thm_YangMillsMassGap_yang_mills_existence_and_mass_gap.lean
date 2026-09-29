-- Prove2me | Theorems.Thm_YangMillsMassGap_yang_mills_existence_and_mass_gap
-- name    : YangMillsMassGap.yang_mills_existence_and_mass_gap
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:07:42.789815+00:00
-- url     : https://prove2.me/theorems/bebeb1dd-a08e-4e71-b411-0a5ef31577fb
-- title:
--   Yang–Mills existence and mass gap
-- statement:
--   **Yang–Mills Existence and Mass Gap** (Jaffe–Witten §4). For every compact simple gauge group $G$, a non-trivial quantum Yang–Mills theory exists on $\mathbb R^4$ and has a mass gap $\Delta>0$. Existence includes the Wightman axioms, which by the reconstruction theorems also give the Osterwalder–Schrader axioms. The mass is required to be finite: $\operatorname{spec}H\neq\{0\}$. The theory is identified as Yang–Mills with gauge group $G$ through the proxy definition `IsNontrivialYangMillsTheory`.
-- source:
--   A. Jaffe, E. Witten, *Quantum Yang–Mills Theory* (Clay Mathematics Institute Millennium Problem description), https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf, §4, 'Yang–Mills Existence and Mass Gap'

module

public import Mathlib
public import Definitions.Def_YMMG_YangMills

public section

namespace YangMillsMassGap
open scoped InnerProductSpace
/-- **Yang–Mills existence and mass gap** (Jaffe–Witten, §4): for every compact simple gauge
group `G`, a non-trivial quantum Yang–Mills theory with gauge group `G` exists on `ℝ⁴`, satisfies
the Wightman axioms, and has a mass gap `Δ > 0` (with finite mass `m < ∞`). -/
theorem yang_mills_existence_and_mass_gap
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (N : ℕ) (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ) (hG : IsCompactSimpleGaugeGroup ρ) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ι : Type) (κ : ι → Type) (_ : ∀ i, Fintype (κ i)) (_ : ∀ i, DecidableEq (κ i))
      (Q : WightmanQFT H ι κ),
      IsNontrivialYangMillsTheory Q ρ ∧ ∃ Δ : ℝ, 0 < Δ ∧ Q.HasMassGap Δ ∧ Q.MassIsFinite := by sorry
end YangMillsMassGap
