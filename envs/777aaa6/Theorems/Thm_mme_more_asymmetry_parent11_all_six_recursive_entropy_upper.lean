-- Prove2me | Theorems.Thm_mme_more_asymmetry_parent11_all_six_recursive_entropy_upper
-- name    : mme_more_asymmetry_parent11_all_six_recursive_entropy_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T05:27:51.833312+00:00
-- url     : https://prove2.me/theorems/d82201d1-1969-4432-8a7f-a70681984258
-- title:
--   Certified recursive maximum-entropy bounds for all six regions of fourth parent (1,1,6)
-- statement:
--   Consider the first positive fourth-parent consumer of the pinned More Asymmetry witness, source owner terms{3}{11}, shape $(1,1,6)$ and global identifier $(0,1)$. Its ordered split rows are $004\mid112$, $013\mid103$, $103\mid013$, and $112\mid004$. Let $\alpha_r$ be its explicit rational split distribution in recursive region $r$, in order $XYZ,XZY,YXZ,YZX,ZXY,ZYX$. For every $r$ and every probability distribution $\rho$ on these four split rows with the same three physical left-coordinate marginals as $\alpha_r$,
--
--   $$H_{\mathrm{nat}}(\rho)=\sum_a -\rho(a)\log\rho(a)\le U_r.$$
--
--   The exact rational bounds are
--
--   $$(U_1,\ldots,U_6)=\left(\frac{61579206213}{50000000000},\frac{123064914207}{100000000000},\frac{12315787553}{10000000000},\frac{61532527549}{50000000000},\frac{123049493181}{100000000000},\frac{61524641541}{50000000000}\right).$$
--
--   The convention is $0\log0=0$. The support uses the actual grades $(0,0,4),(0,1,3),(1,0,3),(1,1,2)$, not shifted Z labels; the source dual offset $(0,0,2)$ is translated exactly. There is no assumed log estimate, optimizer/KKT equation, or exact-marginal matching condition on the auxiliary positive reference distribution. This certifies six recursive maximum-entropy terms for this one source consumer, not the recursive min-of-sums rates, a tensor extraction, or the final matrix-multiplication bound.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Proposition 6.3/Theorem 6.4 and numerical Section 7. Pinned release code_matrix_mult.zip, data/W1.00_2.371339.mat, archive SHA256 a88d211df0a82f0bba0a77ccbad9103064ebef08eea95613e5926a4f666260d8 and member SHA256 783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3. Source TermInfo.Build, RegisterVariablesAndLinearConstraints, GetLagrangeConstraints, PrepareSplits and Dims; owner terms{3}{11}, global identifier (0,1). Rational simplex convention exactly matches the published global witness: 15-digit normalize/round/fix-largest, preserving zero faces. Direct proof dependencies: entropy upper certificate ae0df7ed-d414-4940-996c-8707d2ab69b7 and exact rational logarithm certificate f79fd5f9-9d45-427a-a128-f81b83b98053, both Proved in pinned Mathlib. The emitted numerical data and exact source offsets are defined in mme_more_asymmetry_recursive_parent11_entropy_data.

import Definitions.Def_mme_more_asymmetry_recursive_parent11_entropy_data

open MME.MoreAsymmetryRecursiveWitness11 BigOperators

set_option autoImplicit false

theorem mme_more_asymmetry_parent11_all_six_recursive_entropy_upper (r : Fin 6) (rho : Fin 4 → ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hrhoSum : ∑ a, rho a = 1)
    (hmarg : ∀ (mode : Fin 3) (j : Fin 5),
      mme_modern_marginal (fun a ↦ leftAddress a mode) rho j =
      mme_modern_marginal (fun a ↦ leftAddress a mode)
        (fun a ↦ (alpha r a : ℝ)) j) :
    (∑ a, Real.negMulLog (rho a)) ≤ (entropyUpper r : ℝ) := by sorry
