-- Prove2me | Theorems.Thm_mme_released_recursive_level2_marginals
-- name    : mme_released_recursive_level2_marginals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T22:08:24.388101+00:00
-- url     : https://prove2.me/theorems/75a0e5d2-aa1a-4524-a4d3-d71a13406e4a
-- title:
--   Level-two parent mixtures and grade marginals in closed form
-- statement:
--   The level-two parent mixture of the released recursive construction, in closed form.
--
--   A sum over the admissible splits of a region is first rewritten as a filtered sum over all grade
--   triples, which removes the dependence of the index type on the region. The mixture of a pair of
--   one-letter words is then an explicit quotient of small integers over the scale, and it vanishes
--   unless the two letters are a grade and its complement; on that diagonal it is the region's grade
--   marginal in the given mode.
--
--   Finally, those marginals are given in closed form. In each region exactly one mode has parent grade
--   two, and in that mode the marginal is the triple (s, scale - 2s, s) for the region's own weight
--   parameter s; in the other two modes the marginal is the uniform pair (half the scale, half the
--   scale, 0). So every level-two entropy in the regional rate is either the entropy of a fair coin or a
--   one-parameter entropy in that weight.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_bridge_data
import Theorems.Thm_mme_released_recursive_stage_structure_valid
import Theorems.Thm_mme_released_recursive_level2_shapes
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem mme_released_recursive_level2_marginals :
    (∀ {half : ℕ} {parent : Fin 3 → ℕ} (g : (Fin 3 → Fin (half + 1)) → ℚ),
      ∑ c : RecursiveThinSplit.Split half parent, g c.val =
        ∑ a : Fin 3 → Fin (half + 1),
          if (a 0).val + (a 1).val + (a 2).val = half ∧ ∀ i, (a i).val ≤ parent i then g a
          else 0) ∧
    (∀ (i : Fin 3) (r : Fin 1104), 0 < n2 r → ∀ w : Fin 2 → CompleteSplit.CompleteWord 1,
      mixQ htotal2 n2 m2 (mu2 i) r w = PL i r w) ∧
    (∀ (i : Fin 3) (r : Fin 1104) (w : Fin 2 → CompleteSplit.CompleteWord 1),
      PL i r w =
        (if (w 1 0).val = parent2 r i - (w 0 0).val then (Jm r i (w 0 0) : ℚ) else 0) / (D : ℚ)) ∧
    ∀ (r : Fin 1104) (i v : Fin 3), Jm r i v =
      if parent2 r i = 2 then
        (![(l2At r).2.2, D - 2 * (l2At r).2.2, (l2At r).2.2] : Fin 3 → ℕ) v
      else (![D / 2, D / 2, 0] : Fin 3 → ℕ) v := by sorry
