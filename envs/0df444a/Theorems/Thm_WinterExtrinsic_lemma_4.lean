-- Prove2me | Theorems.Thm_WinterExtrinsic_lemma_4
-- name    : WinterExtrinsic.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:12.744268+00:00
-- url     : https://prove2.me/theorems/bb11ad32-58a7-401f-bba5-ef8b01da26ef
-- title:
--   Lemma 4 — gentle measurement, for states and subnormalized density operators
-- statement:
--   Let $\rho$ be a positive semidefinite operator on a finite-dimensional complex Hilbert space with $\mathrm{Tr}\,\rho \le 1$ (a state when $\mathrm{Tr}\,\rho = 1$, a subnormalized density operator otherwise), and let $X$ be an operator with $0 \le X \le \mathbb 1$. If $\mathrm{Tr}(\rho X) \ge 1 - \lambda$, then
--
--   $$\big\| \rho - \sqrt X\, \rho \sqrt X \big\|_1 \le \sqrt{8\lambda} .$$
--
--   A measurement outcome that is likely on $\rho$ disturbs $\rho$ only slightly. In the proof of Theorem 2 the lemma is applied to the subnormalized operators $\xi'_{j^l}$.
--
--   **Formalization Note** $\sqrt X$ is `cfc Real.sqrt X`; $\|\cdot\|_1$ is `QAlgorithms.traceNorm`, $\mathrm{Tr}\sqrt{M^\dagger M}$ (unhalved, as on the page); $\mathrm{Tr}(\rho X)$ is `effectProb X ρ`. The normalized case is the platform theorem `QAlgorithms.Papers.Independent.Renew46.P43.tenderOperator`.
--
--   Differences from the source:
--   - encoding: two sentences (a state; a subnormalized density operator) → one statement for positive semidefinite $\rho$ with $\mathrm{Tr}\,\rho \le 1$; reason: the state case is the instance $\mathrm{Tr}\,\rho = 1$, so the statement is exactly the conjunction of the two sentences.
-- source:
--   Winter, "Extrinsic" and "intrinsic" data in quantum measurements, arXiv:quant-ph/0109050v3, §II, Lemma 4, p.5 (Lemma V.9 of [27])

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

namespace WinterExtrinsic

open QAlgorithms
open scoped ComplexOrder

/-- Lemma 4 (gentle measurement), for states and subnormalized density operators: if `ρ ≥ 0`,
`Tr ρ ≤ 1`, `0 ≤ X ≤ 1` and `Tr(ρX) ≥ 1 − λ`, then `‖ρ − √X ρ √X‖₁ ≤ √(8λ)`.

Winter, *"Extrinsic" and "intrinsic" data in quantum measurements*, arXiv:quant-ph/0109050v3,
§II, Lemma 4, p.5 (Lemma V.9 of [27]): "For a state ρ and an operator 0 ≤ X ≤ 1, if
Tr(ρX) ≥ 1 − λ, then ‖ρ − √Xρ√X‖₁ ≤ √(8λ). The same is true if ρ is only a subnormalized
density operator."

**Formalization Note.** One statement covers both sentences: a state is a positive semidefinite
`ρ` with `Tr ρ = 1`, a subnormalized density operator one with `Tr ρ ≤ 1`. `√X` is
`cfc Real.sqrt X`; `QAlgorithms.traceNorm` is the unhalved trace norm `Tr √(M†M)`;
`effectProb X ρ = Re Tr(Xρ) = Tr(ρX)`. The normalized case is the platform theorem
`QAlgorithms.Papers.Independent.Renew46.P43.tenderOperator`. -/
theorem lemma_4 {κ : Type} [Fintype κ] [DecidableEq κ] (ρ X : Matrix κ κ ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1) (hX : IsEffect X) (lam : ℝ)
    (h : 1 - lam ≤ effectProb X ρ) :
    traceNorm (ρ - cfc Real.sqrt X * ρ * cfc Real.sqrt X) ≤ Real.sqrt (8 * lam) := by sorry

end WinterExtrinsic
