-- Prove2me | Theorems.Thm_mme_graded_integer_step_low_level_log_recipe
-- name    : mme_graded_integer_step_low_level_log_recipe
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-24T04:02:34.597984+00:00
-- url     : https://prove2.me/theorems/fb00c9d5-f808-4c12-a2b7-bcfbc5088e5d
-- title:
--   One-input graded joint termination at elementary depth
-- statement:
--   Let $D$ be a graded-source integer regional extraction step at level $\ell\leq1$, with physical source predicate $P$, and let $u>\ell$. Choose a nonnegative rate $r$ bounded by the explicit certified logarithmic copy budget of its underlying integer step. For every partition of the physical reference positions by their full cells, there are orientations $z_j\in\{0,1,2\}$ and exact boundary profiles $B_j$ that reproduce the prescribed cell grades and all three mode histograms.
--
--   There is a graded logarithmic joint recipe $E$ for the same source $P$ at level $u$, satisfying
--   $$\operatorname{inputs}(E)=1,\qquad\log\operatorname{outputs}(E)=r,$$
--   with matrix dimensions
--   $$\operatorname{dims}(E)=\left(\prod_j a(B_j,z_j),\ \prod_j b(B_j,z_j),\ \prod_j c(B_j,z_j)\right).$$
--   Here $j$ runs over the chosen reference-cell partition, and $a(B_j,z_j)$, $b(B_j,z_j)$, and $c(B_j,z_j)$ are the three dimensions of the oriented boundary profile. The recipe uses one spatial part and one exact output case, followed by the constructed terminal boundary interface. It retains the original graded source inclusion. No ordinary inclusion of all band words into $P$, whole-window recipe, or additional terminal witness is assumed.
-- source:
--   Graded-source adaptation of Robertboy18's [elementary-depth boundary terminal interface](p2m:theorem/bd0aea3a-f65f-45e6-bba2-7d13ce9492ad) and [ordinary low-level logarithmic recipe](p2m:theorem/20aca569-0844-4792-ad72-9d0f7deed06a), using the [canonical graded integer steps and joint recipes](p2m:theorem/99cd2e8f-ea35-448d-a8e9-757f1b42bb0d). The accompanying parent-window specialization follows Robertboy18's [ordinary parent-window recipe](p2m:theorem/4623db12-9558-436a-9820-c0990c34485e), with parent grading retained explicitly in the source. This is a finite formal composition interface for the [recursive joint construction](p2m:theorem/55bde106-3adc-41ac-bbd9-8e89d799a028), not a new matrix-multiplication exponent claim.

import Definitions.Def_mme_graded_integer_regional_step_data

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.ProfiledCW
  MME.RegionRealization
set_option autoImplicit false

theorem mme_graded_integer_step_low_level_log_recipe
    {ell M upper : ℕ} {P : Predicate M} (D : IntegerStepG ell M P)
    (hlevel : ell ≤ 1) (hupper : ell < upper)
    (part : Partition (fullCell D.step.total D.step.reference))
    (rate : ℝ) (hrate : 0 ≤ rate) (hbudget : rate ≤ D.step.certifiedLogCopies) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.step.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ E : LogJointRecipeG M upper P,
        E.inputs = 1 ∧ E.logOutputs = rate ∧
        E.dims = (∏ j, (profiles j).a (z j),
          ∏ j, (profiles j).b (z j), ∏ j, (profiles j).c (z j)) := by sorry
