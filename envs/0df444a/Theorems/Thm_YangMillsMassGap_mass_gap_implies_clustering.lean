-- Prove2me | Theorems.Thm_YangMillsMassGap_mass_gap_implies_clustering
-- name    : YangMillsMassGap.mass_gap_implies_clustering
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:00:09.765924+00:00
-- url     : https://prove2.me/theorems/4527da72-fa32-41ea-a74c-bddf0882fa7f
-- title:
--   Mass gap implies exponential clustering
-- statement:
--   Let $Q$ be a Wightman QFT whose Hamiltonian has a mass gap $\Delta$. Take any positive constant $C<\Delta$ and any local operator $O$, i.e. a polynomial in fields smeared with test functions supported in a fixed ball, with $\langle\Omega,O\Omega\rangle=0$. Then $|\langle\Omega,O(\vec x)O(\vec y)\Omega\rangle|\le e^{-C|\vec x-\vec y|}$ once $|\vec x-\vec y|$ is sufficiently large, where $O(\vec x)=e^{-i\vec P\cdot\vec x}Oe^{i\vec P\cdot\vec x}$.
-- source:
--   A. Jaffe, E. Witten, *Quantum Yang–Mills Theory* (Clay Mathematics Institute Millennium Problem description), https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf, §5, equation (2)

module

public import Mathlib
public import Definitions.Def_YMMG_WightmanQFT

public section

namespace YangMillsMassGap
open scoped InnerProductSpace
/-- **Clustering from the mass gap** (Jaffe–Witten §5, eq. (2)): if `H` has a mass gap `Δ`, then
for every positive `C < Δ` and every local operator `O` with `⟨Ω, OΩ⟩ = 0`,
`|⟨Ω, O(x⃗)O(y⃗)Ω⟩| ≤ exp(-C|x⃗ - y⃗|)` once `|x⃗ - y⃗|` is sufficiently large, where
`O(x⃗) = e^{-iP⃗·x⃗} O e^{iP⃗·x⃗}`. -/
theorem mass_gap_implies_clustering
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type} {κ : ι → Type} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (Q : WightmanQFT H ι κ) (Δ : ℝ) (hgap : Q.HasMassGap Δ) (C : ℝ) (hC0 : 0 < C)
    (hCΔ : C < Δ) (R : ℝ) (O : Module.End ℂ Q.D) (hO : O ∈ Q.localAlgebra R)
    (hO0 : ⟪Q.Ω, (O Q.ΩD : H)⟫_ℂ = 0) :
    ∃ r₀ : ℝ, ∀ x y : Space, r₀ ≤ dist x y →
      ‖⟪Q.Ω, ((Q.translateOp (ofSpace x) O * Q.translateOp (ofSpace y) O) Q.ΩD : H)⟫_ℂ‖ ≤
        Real.exp (-C * dist x y) := by sorry
end YangMillsMassGap
