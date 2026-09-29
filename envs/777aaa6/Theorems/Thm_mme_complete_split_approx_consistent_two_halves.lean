-- Prove2me | Theorems.Thm_mme_complete_split_approx_consistent_two_halves
-- name    : mme_complete_split_approx_consistent_two_halves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T21:38:03.183603+00:00
-- url     : https://prove2.me/theorems/4b71a175-a646-42b1-bbfc-c167f1bf2a4a
-- title:
--   Approximate complete-profile consistency passes to both literal word halves
-- statement:
--   Let $\ell\ge1$, and let a parent complete word consist of two ordered words of length $2^{\ell-1}$. Suppose a normalized parent profile $\beta$ and normalized child profiles $p,q$ have the exact full-word marginal identities
--   $$
--   \sum_y\beta(x\circ y)=p(x),\qquad \sum_x\beta(x\circ y)=q(y).
--   $$
--   Label each of $N$ positions by a parent complete word. If the parent-word counts differ from $N\beta$ by at most $N\varepsilon$ in every coordinate, then each half-word count differs from its corresponding target $Np$ or $Nq$ by at most $NC\varepsilon$, where $C$ is the number of parent complete words:
--   $$
--   C=3^{2^\ell}.
--   $$
--   The conclusion concerns both deterministic half-labels at the same original $N$ positions and is valid also at $N=0$ under the existing empty-power convention. It is a one-way finite consistency implication, not a construction of a $2N$-position child tensor power or the quantitative recursive extraction theorem. The alphabet-cardinality factor is a conservative bound.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions3.4–3.6 on printed pp.14–15 (complete-word empirical consistency), joint distributions on concatenated words on printed p.14, and Proposition6.3 on printed p.31 (full-profile marginal/mixture identities). https://arxiv.org/abs/2404.16349v2. This is an elementary finite deterministic-coarsening corollary of those semantics; the conservative factor here is not asserted to be the source's recursive 3epsilon-to-epsilon extraction bound.

import Definitions.Def_mme_complete_split_concatenation

open MME MME.CompleteSplit MME.DWZComponentRestriction BigOperators
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_approx_consistent_two_halves {ι : Type u} {ell N : ℕ} (hell : 1 ≤ ell)
    (label : ι → CompleteWord (ell + 1))
    (parent : Profile (ell + 1)) (left right : Profile ell)
    (hleft : ∀ x, ∑ y,
      parent.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        left.probability x)
    (hright : ∀ y, ∑ x,
      parent.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        right.probability y)
    (epsilon : ℝ≥0) (w : PowIndex ι N)
    (h : ApproxConsistent label parent epsilon w) :
    ApproxConsistent (fun a ↦ (completeWordSplitEquiv ell hell (label a)).1)
        left ((Fintype.card (CompleteWord (ell + 1)) : ℝ≥0) * epsilon) w ∧
      ApproxConsistent (fun a ↦ (completeWordSplitEquiv ell hell (label a)).2)
        right ((Fintype.card (CompleteWord (ell + 1)) : ℝ≥0) * epsilon) w := by sorry
