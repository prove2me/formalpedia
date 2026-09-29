-- Prove2me | solution 1 for EmergentGeometry.cutWeight_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:51:49.933173+00:00
-- url     : https://prove2.me/submissions/58faf3eb-0445-4cf4-97a0-854423174fe5

-- Sol generated from Novelty/EmergentGeometryObstructions.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_EmergentGeometryObstructions

/-!
# Obstructions and stability for emergent geometry

Three complementary results about which quantum states can have a geometric
(bulk) dual, and how robust the emergent geometry is.

* **Obstruction.** `no_geometric_dual_of_ghz_type` shows that the entropy
  pattern in which every one-, two- and three-party marginal of a four-party
  state has entropy `1` — the pattern of the four-party GHZ state — is realised
  by *no* bulk geometry whatsoever.  Entanglement alone does not build
  spacetime: only entanglement obeying monogamy does.

* **Stability.** `entropy_lipschitz` shows that the entanglement entropies
  depend Lipschitz-continuously on the bulk geometry: perturbing all areas by a
  total of `ε` perturbs every entropy by at most `ε/2`.  Emergent geometry is
  therefore not an artefact of fine tuning.

* **Identification of the two connectivity notions.**
  `bulkPath_iff_entanglementPath` shows that, in a model without hidden cells,
  the bulk connectivity relation is *exactly* the transitive closure of pairwise
  entanglement: the Einstein–Rosen network and the EPR network coincide as
  graphs.
-/

noncomputable section

open EmergentGeometry

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## A state with no geometric dual -/



/-! ### The obstruction is genuinely new: monogamy is strictly stronger than the
general quantum entropy inequalities -/





/-! ## Stability of the emergent geometry -/





/-! ## The Einstein–Rosen network is the EPR network -/




open EmergentGeometry in
omit [DecidableEq V] in
theorem solution(G G' : BulkGraph V) (f : Region V) :
    |cutWeight G f - cutWeight G' f| ≤ geometryDist G G' := by
  have hsub : cutWeight G f - cutWeight G' f
      = (∑ u, ∑ v, (sepBit (f u) (f v) : ℝ) * (G.weight u v - G'.weight u v)) / 2 := by
    simp only [cutWeight]
    rw [← sub_div]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [hsub, geometryDist, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have habs : |∑ u, ∑ v, (sepBit (f u) (f v) : ℝ) * (G.weight u v - G'.weight u v)|
      ≤ ∑ u, ∑ v, |G.weight u v - G'.weight u v| := by
    calc |∑ u, ∑ v, (sepBit (f u) (f v) : ℝ) * (G.weight u v - G'.weight u v)|
      ≤ ∑ u, |∑ v, (sepBit (f u) (f v) : ℝ) * (G.weight u v - G'.weight u v)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u, ∑ v, |G.weight u v - G'.weight u v| := by
        refine Finset.sum_le_sum fun u _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun v _ => ?_
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (sepBit (f u) (f v) : ℝ))]
        have hle : (sepBit (f u) (f v) : ℝ) ≤ 1 := by
          unfold sepBit; split <;> norm_num
        nlinarith [abs_nonneg (G.weight u v - G'.weight u v)]
  linarith
