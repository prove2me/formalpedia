-- Prove2me | Theorems.Thm_Wolf_commutator_lcs_le
-- name    : Wolf.commutator_lcs_le
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-22T23:49:44.982179+00:00
-- url     : https://prove2.me/theorems/dee48383-646c-4c29-b260-3eaa0f415ded
-- title:
--   Commutator bound for lower central series terms
-- statement:
--   For the lower central series $\Gamma_k$ of a group $G$ (with $\Gamma_0 = G$, $\Gamma_{k+1} = [\Gamma_k, G]$), the commutator of terms satisfies $[\Gamma_k, \Gamma_l] \leq \Gamma_{k+l+1}$. This is the key commutator estimate for Wolf's Lemma 3.7: it controls where commutators of lower-central-series terms land, which is needed to show the successive quotients $\Gamma_k/\Gamma_{k+1}$ are finitely generated. The proof is by induction on $l$ using the Three Subgroups Lemma.

import Definitions.Def_MilnorWolf_Growth
import Mathlib

set_option autoImplicit false

open MilnorWolf
open scoped commutatorElement

theorem Wolf.commutator_lcs_le {G : Type*} [Group G] (k l : ℕ) : ⁅MilnorWolf.lcs G k, MilnorWolf.lcs G l⁆ ≤ MilnorWolf.lcs G (k + l + 1) := by sorry
