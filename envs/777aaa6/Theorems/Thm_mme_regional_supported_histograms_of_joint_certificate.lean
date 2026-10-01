-- Prove2me | Theorems.Thm_mme_regional_supported_histograms_of_joint_certificate
-- name    : mme_regional_supported_histograms_of_joint_certificate
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-30T20:26:47.25558+00:00
-- url     : https://prove2.me/theorems/6fb19583-686c-4404-ae5d-b4bff847672b
-- title:
--   Joint finite certificates realize supported regional child histograms
-- statement:
--   Fix a physical regional position set, a target split address, and a layout of the complete child words as flat CW words. For each cell $c$, provide an integer joint table $J_c(x,y,z)$ and three prescribed marginal histograms $\mu_{i,c,w}$.
--
--   Assume the following exact finite checks:
--
--   * The sum of $J_c$ equals the number of physical positions in cell $c$.
--   * Every triple with positive count has coordinatewise CW support: its three grades at each atomic position sum to two.
--   * Each child word has the grade prescribed by its mode and cell.
--   * The three marginals of $J_c$ are exactly $\mu_{i,c}$.
--
--   Then there is an actual supported triple of flat CW words. Its three words are graded at the target address and, after splitting through the chosen layout, have exactly the three prescribed cell histograms.
--
--   Empty cells and zero table entries are allowed. The proof assigns the joint-table occurrences bijectively to each physical cell fiber, takes the three coordinate projections, and flattens the words through the layout. At level three this supplies the supported target triple needed for positivity of a level-four-to-level-three histogram-window stage. The table and its feasibility checks are hypotheses; this auxiliary theorem does not provide AlphaEvolve's particular table or numerical surplus.
-- source:
--   Auxiliary finite realization derived from platform definitions of recursive CW support, graded words, layouts and cell histograms. Finite assignment uses Mathlib 777aaa61dcd2a1258d2b4962dbe983ede4d23b2e Fintype.equivOfCardEq (Mathlib/Data/Fintype/EquivFin.lean), and Finset.sum_card_fiberwise_eq_card_filter (Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean). Application context: Alman et al., More Asymmetry Yields Faster Matrix Multiplication, Sections 5-6, https://arxiv.org/abs/2404.16349, and level-four rational verification in Dupont et al., https://arxiv.org/html/2608.16884v1#S4. This statement is derived here rather than quoted verbatim.

import Definitions.Def_mme_recursive_yz_compatibility
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_dwz_profiled_regional_positions_data
import Mathlib

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem mme_regional_supported_histograms_of_joint_certificate
    {half R ell L M : ℕ} (parent : Fin R → Fin 3 → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (a : Address half R parent n)
    (positions : Fin L ≃ Position n) (length : L * 2 ^ (ell - 1) = M)
    (J : Cell half R parent → (Fin 3 → CompleteSplit.CompleteWord ell) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ c, ∑ z, J c z = Fintype.card {p : Position n // fullCell htotal a p = c})
    (hsupp : ∀ c z, 0 < J c z → ∀ r,
      (z 0 r).val + (z 1 r).val + (z 2 r).val = 2)
    (hgrade : ∀ c z, 0 < J c z → ∀ i,
      ∑ r, (z i r).val = (c.2.val i).val)
    (hmarg : ∀ i c w, ∑ z ∈ Finset.univ.filter
      (fun z : Fin 3 → CompleteSplit.CompleteWord ell ↦ z i = w), J c z = mu i c w) :
    ∃ x : Fin 3 → ProfiledCW.FineWord M, ProfiledCW.supported x ∧
      ∀ i, Graded htotal i a (ProfiledCW.split positions length (x i)) ∧
        ∀ c w, count (fullCell htotal a) (ProfiledCW.split positions length (x i)) c w =
          mu i c w := by sorry
