-- Prove2me | Theorems.Thm_mme_complete_split_approx_consistent_coarsen
-- name    : mme_complete_split_approx_consistent_coarsen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T21:28:44.859714+00:00
-- url     : https://prove2.me/theorems/60a779c4-ca1b-480a-80e8-3fc9950cc7cc
-- title:
--   Complete-profile consistency survives deterministic coarsening
-- statement:
--   Let A and B be the finite alphabets of complete words at levels ℓ and k. Let π:A→B be a deterministic map, let β be a probability profile on A, and let γ be its exact pushforward:
--   $$\gamma(x)=\sum_{\sigma:\,\pi(\sigma)=x}\beta(\sigma).$$
--   For any sequence of N labelled positions, if its A-counts differ from Nβ pointwise by at most Nε, then its projected B-counts differ from Nγ pointwise by at most N|A|ε. In the existing complete-split consistency notation,
--   $$\operatorname{Consistent}_{\varepsilon}(w,\beta)\Longrightarrow\operatorname{Consistent}_{|A|\varepsilon}(\pi w,\gamma).$$
--   This deliberately conservative finite-alphabet bound supplies a one-way transport to child marginals. It uses the same N positions, not a flattening to 2N positions; it does not reconstruct a joint distribution from its marginals. At N=0 it follows the defined empty-word convention.
-- source:
--   Elementary finite pushforward consequence of the complete empirical-distribution and sup-norm consistency definitions in Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions 3.4–3.6, printed pp.14–15. https://arxiv.org/abs/2404.16349v2. The alphabet-cardinality tolerance is a proved conservative auxiliary estimate, not an assertion that it equals the quantitative tolerance constants in the paper's recursive extraction theorem.

import Definitions.Def_mme_complete_split_profile_projection

open MME MME.CompleteSplit MME.DWZComponentRestriction BigOperators
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_approx_consistent_coarsen {ι : Type u} {ell k N : ℕ}
    (label : ι → CompleteWord ell) (project : CompleteWord ell → CompleteWord k)
    (parent : Profile ell) (child : Profile k)
    (hmarginal : ∀ x, child.probability x =
      ∑ sigma : CompleteWord ell,
        if project sigma = x then parent.probability sigma else 0)
    (epsilon : ℝ≥0) (w : PowIndex ι N)
    (h : ApproxConsistent label parent epsilon w) :
    ApproxConsistent (project ∘ label) child
      ((Fintype.card (CompleteWord ell) : ℝ≥0) * epsilon) w := by sorry
