-- Prove2me | Definitions.Def_Kourovka_Modules_ModuleRealization
-- name    : Kourovka_Modules_ModuleRealization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:45:29.439529+00:00
-- url     : https://prove2.me/theorems/13a01a4a-c48a-4bae-ae8f-719acf8150a3
-- title:
--   Module Realization
-- statement:
--   Definitions and structural lemmas for Module Realization, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ModuleRealization.lean

import Definitions.Def_Kourovka_Modules_SignedTameness
set_option autoImplicit true
noncomputable section
namespace Kourovka.MetabelianEnumeration.ModuleRealization
open FiniteCover ValuationModule SignedTameness TamenessCompactness
variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]
def encodeSigned (p : SignedPolynomial k) : Polynomial k :=
  (p.1, p.2.support.toList.map fun u => (if p.1 then u else -u, p.2 u))
def ActionCompatible (j : Multiplicative M →* G) (t : Fin k → G) : Prop :=
  ∀ u m, j (Multiplicative.ofAdd ((AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) • m)) =
    conjugate (j (Multiplicative.ofAdd m)) (orderedWord t u)
end Kourovka.MetabelianEnumeration.ModuleRealization


