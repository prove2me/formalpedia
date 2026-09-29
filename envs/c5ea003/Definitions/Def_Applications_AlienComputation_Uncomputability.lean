-- Prove2me | Definitions.Def_Applications_AlienComputation_Uncomputability
-- name    : Applications_AlienComputation_Uncomputability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:31:48.123979+00:00
-- url     : https://prove2.me/theorems/f8cf3cdc-a85b-4b3a-bc01-8e5def117a84
-- title:
--   Aether Catalog definitions — Applications_AlienComputation_Uncomputability
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.AlienComputation.Uncomputability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/AlienComputation/Uncomputability.lean by skeleton subtraction
import Mathlib

/-!
# Substrate-independent uncomputability and the oracle (hypercomputation) barrier

**Research theme: Computational Complexity of Alien Civilizations.**

This file formalizes the claim that the *undecidability of self-reference* is a
theorem about the structure of computation itself, not about any particular
machine model, biology, or physics.  We model an arbitrary notion of computation
abstractly and prove that the diagonal argument bites in **every** such model —
and, crucially, that it continues to bite even when the model is granted an
**arbitrary oracle**, i.e. an unrestricted (possibly hyper-computational)
resource.  Thus even a civilization with hypercomputers faces an *analogous*
barrier: the jump of a class is never internal to the class.

## Design

A `ComputationModel` is *any* type `Pgm` of "programs" together with a Boolean
acceptance relation `accepts : Pgm → Pgm → Bool` (`accepts p q =` "program `p`
accepts the code of program `q`").  No computability, finiteness, or structure is
assumed on `Pgm`; the results below are therefore forced on any civilization
whose programs can be coded by the same objects they act on.

## Main results

* `AlienComputation.ComputationModel.diagonal_not_realized` : the diagonal
  behaviour is realized by no program (abstract halting-problem undecidability).
* `AlienComputation.ComputationModel.exists_undecidable` : every model has a
  decision behaviour outside the range of its programs.
* `AlienComputation.substrate_independent` : the previous statement holds for
  *every* model, with no hypotheses — the obstruction is model-independent.
* `AlienComputation.OracleModel.jump_not_internal` : even a model equipped with
  an arbitrary oracle cannot internally decide its own jump.
* `AlienComputation.hypercomputation_barrier` : the relativized barrier holds for
  every oracle whatsoever.
-/

namespace AlienComputation

universe u


/-- An **abstract model of computation**: a type of programs together with a
Boolean acceptance relation on (program, program-code) pairs.  Deliberately
free of any Turing/λ/physical structure, so that theorems about it are
substrate-independent. -/
structure ComputationModel where
  /-- The type of programs / codes of the model. -/
  Pgm : Type u
  /-- `accepts p q` : program `p` halts-and-accepts on the code of program `q`. -/
  accepts : Pgm → Pgm → Bool

namespace ComputationModel

variable (M : ComputationModel)

/-- The **diagonal behaviour** of a model: the decision procedure that, on input
`q`, returns the opposite of what `q` does to its own code. -/
def diagonal : M.Pgm → Bool := fun q => !(M.accepts q q)



end ComputationModel


/-!
## The hypercomputation barrier

We now give the model an *arbitrary* oracle `oracle : Pgm → Bool`.  The field is
completely unconstrained: it may be any function, including one that is not
computable by any conventional machine.  This is the mathematical stand-in for a
"hypercomputational resource".  The programs' acceptance relation may consult the
oracle in any way whatsoever — this is already subsumed by allowing `accepts` to
be arbitrary.  We show the diagonal obstruction is *invariant* under this
enrichment: the jump of the class is never internal to the class.
-/

/-- A computation model enriched with an **arbitrary oracle** — a stand-in for an
unrestricted hyper-computational resource. -/
structure OracleModel where
  /-- The type of (oracle-)programs. -/
  Pgm : Type u
  /-- An arbitrary, possibly non-computable oracle available to every program. -/
  oracle : Pgm → Bool
  /-- Oracle-relative acceptance. -/
  accepts : Pgm → Pgm → Bool

namespace OracleModel

variable (M : OracleModel)

/-- The relativized jump: the diagonal behaviour of the oracle-model. -/
def jump : M.Pgm → Bool := fun q => !(M.accepts q q)


end OracleModel


end AlienComputation


