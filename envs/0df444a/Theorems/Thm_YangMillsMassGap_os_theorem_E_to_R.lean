-- Prove2me | Theorems.Thm_YangMillsMassGap_os_theorem_E_to_R
-- name    : YangMillsMassGap.os_theorem_E_to_R
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T16:46:09.222293+00:00
-- url     : https://prove2.me/theorems/b3f7a688-2220-47c6-b6ee-fc010040be72
-- title:
--   Osterwalder–Schrader Theorem E → R (as stated in 1973)
-- statement:
--   **Theorem E→R** (Osterwalder–Schrader 1973, §3, as stated there). Given a sequence of Euclidean Green's functions satisfying E0–E4, there is a unique sequence of Wightman distributions satisfying R0–R5 whose Euclidean restriction it is.
--
--   **Caveat:** the 1973 proof contains an error (Lemma 8.8). Osterwalder and Schrader's 1975 sequel proves reconstruction only under an additional linear growth condition. Whether E0–E4 alone suffice should be checked before this is kept as a milestone.
-- source:
--   K. Osterwalder, R. Schrader, *Axioms for Euclidean Green's Functions*, Commun. Math. Phys. 31, 83–112 (1973), https://doi.org/10.1007/BF01645738, p. 88, Theorem E→R; proof in §4; see also Osterwalder–Schrader, Commun. Math. Phys. 42 (1975) 281–305

module

public import Mathlib
public import Definitions.Def_YMMG_WightmanAxioms

public section

namespace YangMillsMassGap
/-- **Theorem E → R** (Osterwalder–Schrader 1973, §3, as stated there): to a sequence of
Euclidean Green's functions satisfying `E0`–`E4` there corresponds a unique sequence of Wightman
distributions satisfying `R0`–`R5`, of which it is the Euclidean restriction. -/
theorem os_theorem_E_to_R (S : DistributionFamily) (hS : SatisfiesOSAxioms S) :
    ∃ W : DistributionFamily, SatisfiesWightmanAxioms W ∧ IsEuclideanRestriction W S ∧
      ∀ W' : DistributionFamily, SatisfiesWightmanAxioms W' → IsEuclideanRestriction W' S →
        W' = W := by sorry
end YangMillsMassGap
