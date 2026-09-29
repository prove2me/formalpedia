-- Prove2me | Theorems.Thm_YangMillsMassGap_os_theorem_R_to_E
-- name    : YangMillsMassGap.os_theorem_R_to_E
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T16:42:59.541642+00:00
-- url     : https://prove2.me/theorems/6c5fd63c-a06d-441b-818d-747d4d425f18
-- title:
--   Osterwalder–Schrader Theorem R → E
-- statement:
--   **Theorem R→E** (Osterwalder–Schrader 1973, §3). Given a sequence of Wightman distributions satisfying R0–R5, there is a corresponding sequence of Euclidean Green's functions with properties E0–E4. The correspondence is that $\mathfrak S$ is the Euclidean restriction of the analytic continuation of $\mathfrak W$. The Green's functions are unique as elements of ${}^0\mathcal S'$, i.e. unique on test functions that vanish with all derivatives at coinciding points.
-- source:
--   K. Osterwalder, R. Schrader, *Axioms for Euclidean Green's Functions*, Commun. Math. Phys. 31, 83–112 (1973), https://doi.org/10.1007/BF01645738, p. 88, Theorem R→E; proof in §5

module

public import Mathlib
public import Definitions.Def_YMMG_WightmanAxioms

public section

namespace YangMillsMassGap
/-- **Theorem R → E** (Osterwalder–Schrader 1973, §3): to a sequence of Wightman distributions
satisfying `R0`–`R5` there corresponds a sequence of Euclidean Green's functions satisfying
`E0`–`E4` (their Euclidean restriction), unique as elements of `⁰𝒮'`. -/
theorem os_theorem_R_to_E (W : DistributionFamily) (hW : SatisfiesWightmanAxioms W) :
    ∃ S : DistributionFamily, SatisfiesOSAxioms S ∧ IsEuclideanRestriction W S ∧
      ∀ S' : DistributionFamily, SatisfiesOSAxioms S' → IsEuclideanRestriction W S' →
        ∀ (n : ℕ) (f : SchwartzMap (Config n) ℂ), VanishesOnCoincidences f → S' n f = S n f := by sorry
end YangMillsMassGap
