-- Prove2me | Theorems.Thm_Erdos180_proposedFamily_not_compact_of_bounds
-- name    : Erdos180.proposedFamily_not_compact_of_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:11:38.813984+00:00
-- url     : https://prove2.me/theorems/48308e71-43e8-47a4-9ca7-2e0f5696eff1
-- title:
--   Two bounds in the same regime refute compactness
-- statement:
--   If $\mathrm{ex}(n,\mathcal{F}) = o(n^{4/3})$ while every member satisfies
--   $\mathrm{ex}(n,F) \ge c\,n^{4/3}$ eventually with $c > 0$, then $\mathcal{F}$ is not compact.
--
--   Indeed compactness would give some $F \in \mathcal{F}$ and $C > 0$ with
--   $\mathrm{ex}(n,F) \le C\,\mathrm{ex}(n,\mathcal{F})$ for large $n$, forcing
--   $c\,n^{4/3} \le C \cdot o(n^{4/3})$, which fails for large $n$. This is the logical shape of
--   Theorem 1.1: the family bound is smaller than every member bound by more than a constant
--   factor.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L4279-L4288

import Definitions.Def_erdos180_core4
import Init.Prelude

open Erdos180
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos180.proposedFamily_not_compact_of_bounds
    (hupper : FamilyLittleO proposedFamily)
    (hlower : UniformMemberLower proposedFamily manuscriptLowerConstant) :
    ¬ IsCompactFamily proposedFamily := by sorry
