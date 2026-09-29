-- Prove2me | Theorems.Thm_groupCohomology_coindIso_hom_eq_map_subtype_comp_map_eval_one
-- name    : groupCohomology.coindIso_hom_eq_map_subtype_comp_map_eval_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/ca78747e-d8f3-5ea9-9b25-b56673c88948
-- title:
--   Shapiro's isomorphism as restriction followed by evaluation at 1
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $S \le G$ a subgroup and $A$ an object of `Rep k S`, i.e. a $k$-linear representation of $S$; let $n$ be a natural number. Write $\mathrm{coind}_S^G A$ for `Rep.coind S.subtype A`, Mathlib's coinduced representation of $G$ along the inclusion $S \hookrightarrow G$, and $\mathrm{res}^G_S$ for restriction of representations along that inclusion. Suppose given a morphism $\mathrm{ev}$ of representations of $S$ from $\mathrm{res}^G_S \mathrm{coind}_S^G A$ to $A$ which is assumed to act on underlying elements by evaluation at the identity: for every $f$ in the coinduced representation, $\mathrm{ev}(f) = f(1)$, where $f$ is viewed as a function $G \to A$. The conclusion identifies the forward direction of Mathlib's isomorphism `groupCohomology.coindIso A n`, from $H^n(G, \mathrm{coind}_S^G A)$ to $H^n(S, A)$, with the composite of the restriction map `groupCohomology.map S.subtype (𝟙 _) n`, induced by the inclusion $S.\mathrm{subtype}$ together with the identity on $\mathrm{res}^G_S \mathrm{coind}_S^G A$, followed by the coefficient map `groupCohomology.map (MonoidHom.id S) ev n` induced by $\mathrm{ev}$; that is, $H^n(\mathrm{ev}) \circ \mathrm{res}^G_S$.
--
--   This is the classical concrete form of Shapiro's lemma: a cohomology class of a coinduced module is transported to the subgroup by restricting and then evaluating cochains at the identity, in every degree and with no hypothesis of finite index. It is used in the idelic cohomology computations of the project, for instance in the local-coordinate description of the cohomology of the idèles and in the comparison of corestriction with the connecting map for induced modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_coindIso_hom_eq_map_subtype_comp_map_eval_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.coindIso_hom_eq_map_subtype_comp_map_eval_one
    {k G : Type u} [CommRing k] [Group G] {S : Subgroup G} (A : Rep k S) (n : ℕ)
    (ev : Rep.res S.subtype (Rep.coind S.subtype A) ⟶ A)
    (hev : ∀ f : Rep.res S.subtype (Rep.coind S.subtype A), ev.hom f = (f : G → A) 1) :
    (groupCohomology.coindIso A n).hom =
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.coind S.subtype A))) n ≫
        groupCohomology.map (MonoidHom.id S) ev n := by sorry
