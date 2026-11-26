-- Prove2me | Theorems.Thm_exists_isWContractibleRing
-- name    : exists_isWContractibleRing
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T12:28:34.110955+00:00
-- url     : https://prove2.me/theorems/810a8fdf-1968-4d86-9d77-9e9763ff93c2
-- title:
--   Lemma 2.4.9 — every ring has a faithfully flat ind-étale w-contractible cover
-- statement:
--   Let $R$ be a commutative ring. Then there exists a commutative $R$-algebra $S$ such that
--
--   1. $S$ is ind-étale over $R$, i.e. a filtered colimit of étale $R$-algebras;
--   2. $S$ is faithfully flat over $R$;
--   3. $S$ is **w-contractible**.
--
--   Here a ring $S$ is called w-contractible when $\operatorname{Spec} S$ is a w-local spectral space (its closed points form a closed subset and every point specializes to a unique closed point), the localization of $S$ at every maximal ideal is a strictly henselian local ring, and the space $\pi_0(\operatorname{Spec} S)$ of connected components is extremally disconnected.
--
--   This lemma provides, for every affine scheme, a pro-étale cover on which every further pro-étale cover splits; it is the source of the local contractibility of the pro-étale topos.
--
--   **Formalization Note** The paper defines w-contractible by a lifting property (Definition 2.4.1: every faithfully flat ind-étale map out of the ring has a section) and proves the description used here as Lemmas 2.2.9, 2.4.2 and 2.4.8. The Lean class `IsWContractibleRing` is that description, not Definition 2.4.1. Likewise `WLocalSpace` follows Lemma 2.1.4 rather than Definition 2.1.1. $R$ and $S$ live in one universe.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Lemma 2.4.9 (p. 14 of the arXiv v2 PDF). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/WContractible.lean, lines 813-823 (`exists_isWContractibleRing`).

import Mathlib
import Definitions.Def_ProEtale_Algebra_IndEtale
import Definitions.Def_ProEtale_Algebra_WContractible
import Definitions.Def_ProEtale_Algebra_WLocal
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe u
open PrimeSpectrum TopologicalSpace
variable {R : Type u} [CommRing R]
variable (R)

theorem exists_isWContractibleRing :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.IndEtale R S ∧ Module.FaithfullyFlat R S ∧ IsWContractibleRing S := by sorry
