-- Prove2me | Definitions.Def_Tropical_TropicalAlgebra_TropicalTDLPEigenAttack
-- name    : Tropical_TropicalAlgebra_TropicalTDLPEigenAttack
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:33:11.91613+00:00
-- url     : https://prove2.me/theorems/3fc43737-9f9d-42ae-8d88-c127c08e3904
-- title:
--   Aether Catalog definitions — Tropical_TropicalAlgebra_TropicalTDLPEigenAttack
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.TropicalAlgebra.TropicalTDLPEigenAttack`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/TropicalAlgebra/TropicalTDLPEigenAttack.lean by skeleton subtraction
import Mathlib

/-!
# A tropical discrete-logarithm counterexample on eigenlines

This file formalizes a small, self-contained counterexample to the security of a
naive *tropical discrete logarithm problem* (TDLP).

We work over `Nat` (the min-plus / tropical semiring carrier, ignoring `+∞`) to
avoid the complications of `WithTop` and partial subtraction.  The "scalar
multiplication" of the min-plus semiring is ordinary addition `λ + x`, and the
group operation that hides the secret exponent `k` is iterated min-plus matrix
application.

The two headline results are:

* `oneByOne_tropical_iterate`: applying the `1×1` tropical matrix with entry `λ`
  exactly `k` times sends `x` to `k * λ + x`.
* `tdlp_recover_oneByOne`: when `λ = 1`, the secret exponent `k` is recovered
  from a single input/output pair by ordinary subtraction `output - input = k`.

The abstract version `iterate_eigenline_attack` shows the same collapse happens
for *any* scalar-equivariant tropical-linear map restricted to one of its
eigenlines, with the coordinate-wise recovery statement
`tdlp_recover_eigenline`.
-/

namespace Catalog.Tropical.TropicalTDLPEigenAttack

/-! ## The 1×1 case -/




/-! ## The abstract eigenline attack -/

/-- A tropical vector indexed by `ι`. -/
abbrev Vec (ι : Type) := ι → Nat

/-- Tropical scalar addition: add the scalar `c` to every coordinate. -/
def tropScalarAdd {ι : Type} (c : Nat) (v : Vec ι) : Vec ι := fun i => c + v i

/-- A map `F` is scalar-equivariant if it commutes with tropical scalar addition. -/
def ScalarEquivariant {ι : Type} (F : Vec ι → Vec ι) : Prop :=
  ∀ (c : Nat) (v : Vec ι), F (tropScalarAdd c v) = tropScalarAdd c (F v)

/-- `v` is a tropical eigenvector of `F` with eigenvalue `lam`. -/
def IsTropicalEigen {ι : Type} (F : Vec ι → Vec ι) (v : Vec ι) (lam : Nat) : Prop :=
  F v = tropScalarAdd lam v




end Catalog.Tropical.TropicalTDLPEigenAttack


