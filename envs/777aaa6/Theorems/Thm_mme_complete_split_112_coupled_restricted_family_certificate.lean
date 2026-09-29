-- Prove2me | Theorems.Thm_mme_complete_split_112_coupled_restricted_family_certificate
-- name    : mme_complete_split_112_coupled_restricted_family_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T22:27:04.730449+00:00
-- url     : https://prove2.me/theorems/3e8b92e5-3730-4be5-9d56-ad6f0c9c3900
-- title:
--   Actual coupled112 C-tensor family survives all complete-profile filters
-- statement:
--   Fix a field, a CW parameter $q$, a rational profile parameter $p$, and natural counts $L+G=N$ with $L=2Np$. Suppose a concrete induced primary-hash family has $A$ outer fibers, each of positive common size $H$, at the exact coupled-address marginals. Let the three normalized complete profiles equal the actual $112$ formulas: the first two are uniform on $01,10$, and the third has masses $p,1-2p,p$ on $02,11,20$.
--
--   For every nonnegative tolerance $\epsilon$, the simultaneous complete-profile restriction of the actual coupled tensor power contains a genuine family of $A$ C-tensors over $\langle1,H,1\rangle$, each of whose matrix-multiplication components has volume
--
--   $$q^{4G+2L}.$$
--
--   The source tensor is literally the all-three-mode complete-profile restriction of $\operatorname{coupledObj}_q^{\otimes2N}$, using its actual lifted coordinate basis and the complete fine-word labels. The family certificate includes the linear restriction and each star's concrete grading and component isomorphisms.
--
--   Only the finite induced address family, compatible integer counts and literal profile equalities are hypotheses. The four-block support, matrix-multiplication block identifications, coordinate-basis grading facts and rejection-to-mismatch conditions are discharged by the proof. This is a finite restricted-source certificate, not an asymptotic scalar value, an existence theorem for the hash family, or the full numerical witness's feasibility.
-- source:
--   Coppersmith and Winograd, Matrix multiplication via arithmetic progressions (1990), journal p270, coupled four-block constituent and balanced N,N / L,L,2G marginal profile. All-three-mode restricted-source semantics: Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4–3.6 printed pp14–15 and level-laser interfaces Proposition6.3/Theorem6.4 pp31–32. Explicit112 complete profiles: OSF https://osf.io/mw5ak/ code_matrix_mult.zip v1, src/evaluation/TermInfoLv2.m lines114–117 and134–146. This theorem is the finite induced-family realization inside those full profiles; it does not claim the paper's full asymptotic recursion or a scalar optimized value. It composes the public concrete four-block, basis-label, exact histogram/mismatch, and generic restricted-family certificates.

import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Definitions.Def_mme_TypeGrading_kron
import Theorems.Thm_mme_complete_split_112_disallowed_word_mismatches_exact_address
import Theorems.Thm_mme_complete_split_112_coupled_basis_label_certificate
import Theorems.Thm_mme_complete_split_112_concrete_four_block_certificate
import Theorems.Thm_mme_complete_split_primary_hash_family_restricted_Ctensor_certificate

set_option autoImplicit false

open MME MME.CompleteSplit MME.CompleteSplit112 MME.DWZComponentRestriction
open CoupledCTensorPackaging
open scoped NNReal

universe u

theorem mme_complete_split_112_coupled_restricted_family_certificate
    {K : Type u} [Field K] (q : ℕ) {N L G A H : ℕ}
    (p : ℚ) (hLG : L + G = N) (hLp : (L : ℚ) = (2 * N : ℕ) * p)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (beta : Fin 3 → Profile 2)
    (hbeta : ∀ mode sigma,
      (beta mode).probability sigma = (profileProbability p mode sigma : ℝ))
    (epsilon : ℝ≥0) :
    Nonempty
      (CTensorOneHOneFamilyCertificate
        (restrictedPower (coupledObj K q) (liftedCoordBasis K q)
          (fun mode ↦ fineWord mode ∘ liftedCoordGrade q mode)
          beta epsilon (2 * N))
        A H (q ^ (4 * G + 2 * L))) := by sorry
