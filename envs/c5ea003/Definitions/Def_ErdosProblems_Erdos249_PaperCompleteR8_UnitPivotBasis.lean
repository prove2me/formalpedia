-- Prove2me | Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR8_UnitPivotBasis
-- name    : ErdosProblems_Erdos249_PaperCompleteR8_UnitPivotBasis
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T13:46:37.406523+00:00
-- url     : https://prove2.me/theorems/00e6fa9c-ae82-4841-b1e0-4e137b261e2c
-- title:
--   Unit-pivot basis of a relation module
-- statement:
--   Defines a system over a commutative ring with original indices $I$, retained indices $J$ mapped into $I$, linearly independent retained values, and finite reconstruction coefficients. Rows indexed by the omitted part of $I$ form a basis of the evaluation map’s relation module.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos249/PaperCompleteR8/UnitPivotBasis.lean#L35-L70
--   Supporting source declaration: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos249/PaperCompleteR8/UnitPivotBasis.lean#L212-L235

import Mathlib
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false

/-!
# Unit-pivot bases of relation modules

Round 8. New proof source; no local compiler was available.
All indices may be infinite: the source of evaluation is a `Finsupp`, not an
unrestricted product. In the finite application it is the ordinary free module
on all channels. The proof is valid over a commutative ring, in particular Z.

Pinned API source: mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6.
`Finsupp.linearCombination`, its single and composition rules, and
`Finsupp.mem_span_range_iff_exists_finsupp` are in
Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean.
`Finsupp.lhom_ext`, `Finsupp.lapply` are in
Mathlib/LinearAlgebra/Finsupp/Defs.lean.
`Module.Basis.span` and `Module.Basis.coe_span_apply` are in
Mathlib/LinearAlgebra/Basis/Basic.lean.
`Module.Basis.map` is in Mathlib/LinearAlgebra/Basis/Defs.lean.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR8.UnitPivot

open scoped BigOperators

variable {R I J M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Data for a generating family with an explicitly retained independent
subfamily. `coeff` is a finite normal form for each original channel. -/
structure System (R I J M : Type*) [CommRing R] [AddCommGroup M] [Module R M] where
  value : I → M
  keep : J → I
  independent : LinearIndependent R (fun j => value (keep j))
  coeff : I → J →₀ R
  reconstruct : ∀ i,
    Finsupp.linearCombination R (fun j => value (keep j)) (coeff i) = value i

namespace System

variable (D : System R I J M)









/-- Only a non-retained coordinate is used as a pivot. -/
def Omitted := { i : I // i ∉ Set.range D.keep }







































end System

end ErdosProblems.Erdos249.PaperCompleteR8.UnitPivot

namespace ErdosProblems.Erdos249.PaperCompleteR8.UnitPivot.System

variable {R I J M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (D : System R I J M)



noncomputable instance omittedFintype [Fintype I] : Fintype D.Omitted := by
  classical
  change Fintype {i : I // i ∉ Set.range D.keep}
  infer_instance





end ErdosProblems.Erdos249.PaperCompleteR8.UnitPivot.System


