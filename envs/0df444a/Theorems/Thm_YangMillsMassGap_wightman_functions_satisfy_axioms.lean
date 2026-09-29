-- Prove2me | Theorems.Thm_YangMillsMassGap_wightman_functions_satisfy_axioms
-- name    : YangMillsMassGap.wightman_functions_satisfy_axioms
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T16:34:14.222254+00:00
-- url     : https://prove2.me/theorems/0b922b37-e965-4049-b073-fce332211283
-- title:
--   Wightman distributions of a scalar field satisfy R0–R5
-- statement:
--   Let $Q$ be a Wightman quantum field theory, and let $\varphi_{i,c}$ be a component of a Lorentz-scalar multiplet. Then there is a family of tempered distributions $\mathfrak W_n$ with $\mathfrak W_n(f_1\otimes\cdots\otimes f_n)=\langle\Omega,\varphi_{i,c}(f_1)\cdots\varphi_{i,c}(f_n)\Omega\rangle$, and this family satisfies the Wightman axioms R0–R5.
-- source:
--   Streater–Wightman (1964), §3.3–3.4 (properties of vacuum expectation values); A. Jaffe, E. Witten, *Quantum Yang–Mills Theory* (Clay Mathematics Institute Millennium Problem description), https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf, §3

module

public import Mathlib
public import Definitions.Def_YMMG_WightmanQFT

public section

namespace YangMillsMassGap
/-- The vacuum expectation values of a Lorentz-scalar hermitian field component of a Wightman
quantum field theory define Wightman distributions satisfying `R0`–`R5`. -/
theorem wightman_functions_satisfy_axioms
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type} {κ : ι → Type} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (Q : WightmanQFT H ι κ) (i : ι) (c : κ i) (hi : Q.IsScalarMultiplet i) :
    ∃ W : DistributionFamily, Q.IsWightmanFamilyOf i c W ∧ SatisfiesWightmanAxioms W := by sorry
end YangMillsMassGap
