-- Prove2me | Theorems.Thm_CouretOaiBridge01_StatusTransport_AdversarialCases_axis_locality_controls
-- name    : CouretOaiBridge01.StatusTransport.AdversarialCases.axis_locality_controls
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:00:51.223894+00:00
-- url     : https://prove2.me/theorems/3d681133-d86e-4c16-84ff-17f1b6040fa6
-- title:
--   Four local invalidation controls
-- statement:
--   For change records with the named field true and all others false, noveltyChanged does not invalidate replay; diffusionChanged does not invalidate semantics; dependenciesChanged does invalidate replay; semanticChanged does invalidate novelty. $$I_{replay}(novelty)=0,\quad I_{semantic}(diffusion)=0,\quad I_{replay}(dependencies)=1,\quad I_{novelty}(semantic)=1.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_06_AdversarialCases.lean#L161-L167, lines 161–167; source file SHA-256 20b6292d6d043a85b3229ffe64c504f69f5c21240583c269d077c13cced07471; theorem CouretOaiBridge01.StatusTransport.AdversarialCases.axis_locality_controls

import Definitions.Def_Couret_STAT_TRANS_06_AdversarialCases_e73cf4a1e1dc
import Mathlib.Data.Set.Basic
import Definitions.Def_Couret_STAT_TRANS_05_MutationSuite_39e36fa4811a

/-!
# STAT-TRANS-06 — Adversarial matrix and scientific case encodings

Finite, executable mutation oracles. These assertions test the current policy,
not the truth of any scientific claim. A bounded walk is not a formal
replacement for arbitrary Reach; positive Reach witnesses are established
in STAT_TRANS_05, and these oracles test negative paths on tiny graphs.

No RH claim. No external novelty claim. No publication-status promotion.
-/

namespace CouretOaiBridge01
namespace StatusTransport
namespace AdversarialCases

open MutationSuite





/-! Mixed graph from STAT-TRANS-05: A -> B proof, A -> C replay,
    B -> D novelty, C -> D documentary. -/



















/-! G30: A finite certificate, B a local derived statement, C an
    unsupported global extension, D a documentary pointer to C.
    There is intentionally no proof bridge to C. -/




/-! T16: A abstract equivalence theorem, B fixed-modulus
    instantiation, C derived mathematical claim, D novelty audit. -/




/-! Cayley: A primary prior-art result, B originality review,
    C public review document, D independently audited mathematical
    proof. Only the bibliographic channel A -> B is licensed. -/




/-! OAI-7/8: A verifier/toolchain, B replay result,
    C published narrative, D bibliographic originality.
    A comparison pass is not a novelty or publication certificate. -/

theorem axis_locality_controls :
    Delta.invalidatesReplay { noveltyChanged := true } = false ∧
    Delta.invalidatesSemantic { diffusionChanged := true } = false ∧
    Delta.invalidatesReplay { dependenciesChanged := true } = true ∧
    Delta.invalidatesNovelty { semanticChanged := true } = true := by sorry


end AdversarialCases
end StatusTransport
end CouretOaiBridge01
