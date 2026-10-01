-- Prove2me | Theorems.Thm_mme_graded_regional_tolerance_window_stage
-- name    : mme_graded_regional_tolerance_window_stage
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-24T01:45:46.523799+00:00
-- url     : https://prove2.me/theorems/eb6196aa-a575-44a7-9fed-0707feda27f3
-- title:
--   Graded regional extraction for a full child tolerance window
-- statement:
--   Fix a central integer regional step, including its parent types, split counts, reference address, physical positions, minimum scale, and repair scale. Let $\delta\ge0$ be a child-profile tolerance, let $\varepsilon>0$ be a parent tolerance, and let $r\ge0$ be a logarithmic rate. Assume the explicit size test for $\varepsilon$ and a uniform finite-loss scalar budget of at least $r$ for every admissible exact child profile within $\delta$ of the central one. Also assume that the parent-graded part of the central parent window of radius $\varepsilon+2\delta$ lies in the desired source predicate $S$.
--
--   There is then a graded regional extraction stage from $S$ to the entire child window, with rate $r$. If $H$ is the number of physical child positions, $C$ the number of split cells, and $A$ the complete-word alphabet size, the number of exact cases is at most
--
--   $$
--   (H+1)^{3CA}.
--   $$
--
--   Every CW-supported triple in the child window belongs to exactly one case. Consequently, if the window contains such a triple, the stage has at least one case. The construction enumerates the distinct realized histograms throughout the tolerance band; it does not require those histograms to equal the central profile. The uniform scalar budget and the graded source inclusion are hypotheses of this construction lemma.
-- source:
--   Graded-source adaptation of raresbuhai's [ordinary tolerance-window step family](p2m:theorem/8d5922ba-ef7d-4b2e-8ef7-c77527cea84f), [accepted proof](p2m:solution/08deb303-0e4b-483f-828c-b099e373d0d8). The construction reuses the accepted prescribed-histogram cover, supported-histogram admissibility, parent-mixture Lipschitz estimate, and target-marginal identities. The tolerance-window interpretation follows Alman, Duan, Vassilevska Williams, Xu, Xu, and Zhou, More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Theorem 6.4. This statement adapts the published formal interfaces; it is not a verbatim theorem from the paper.

import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_regional_tolerance_window_data

open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
set_option autoImplicit false

theorem mme_graded_regional_tolerance_window_stage
    {ell M : ℕ} {P S : Predicate M} (D : IntegerStep ell M P)
    (delta eps rate : ℝ) (hdelta : 0 ≤ delta) (heps : 0 < eps)
    (hrate : 0 ≤ rate)
    (hsize : (8 * D.repairScale : ℝ) *
      (25 * D.R * (Fintype.card (CompleteWord ell) : ℝ) ^ 2) ≤
        (D.minimum : ℝ) * eps ^ 2)
    (hsource : ∀ i x,
      ParentGraded D.parent D.n i (split D.positions D.length x) →
      parentWindow D (eps + 2 * delta) i x → S i x)
    (hbudget : ∀ mu : WindowProfile D, WindowAdmissible D mu →
      (∀ i, WindowClose D delta i (mu i)) →
        rate ≤ windowLogBudget D mu eps) :
    ∃ E : LogPartStageG M ell S (childWindow D delta),
      E.rate = rate ∧
      E.types ≤ (Fintype.card (Position D.n) + 1) ^
        (3 * Fintype.card (Cell D.half D.R D.parent) *
          Fintype.card (CompleteWord ell)) ∧
      ((∃ x : Fin 3 → FineWord M,
        supported x ∧ ∀ i, childWindow D delta i (x i)) → 1 ≤ E.types) := by sorry
