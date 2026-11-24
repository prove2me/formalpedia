-- Prove2me | Theorems.Thm_acyclic_orientation_maximal_unwinnable_correspondence_and_degree
-- name    : acyclic_orientation_maximal_unwinnable_correspondence_and_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:54:01.098878+00:00
-- url     : https://prove2.me/theorems/5609974b-99de-4752-9dc7-259808027068
-- title:
--   acyclic orientation maximal unwinnable correspondence and degree: acyclic orientation maximal unwinnable correspondence and degree
-- statement:
--   The map sending an acyclic orientation with source $q$ to the divisor
--   $v \mapsto \operatorname{indeg}(v) - \delta_{v,q}$ is injective, and every maximal
--   unwinnable divisor has degree $g - 1$. The divisor used here differs from
--   $D(\mathcal{O})$ by a fixed divisor, so injectivity is equivalent.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 4.9(3)
--   for the injectivity claim.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L372-L395
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L372-L395

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem acyclic_orientation_maximal_unwinnable_correspondence_and_degree
    {G : CFGraph} (h_conn : graph_connected G) (q : G.V) :
    (Function.Injective (λ (O : {O : CFOrientation G // is_acyclic G O ∧ is_source G O q}) =>
      λ v => (indeg G O.val v) - if v = q then 1 else 0)) ∧
    (∀ D : CFDiv G, maximal_unwinnable G D → deg D = genus G - 1) := by sorry
