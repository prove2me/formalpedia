-- Prove2me | Definitions.Def_Geometry_HomotopyTypeTheory_HomotopyTypeTheory_StratifiedInterchange
-- name    : Geometry_HomotopyTypeTheory_HomotopyTypeTheory_StratifiedInterchange
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T12:20:17.618664+00:00
-- url     : https://prove2.me/theorems/39565e5a-d51b-4691-b229-aa25f852a7b3
-- title:
--   Aether Catalog definitions — Geometry_HomotopyTypeTheory_HomotopyTypeTheory_StratifiedInterchange
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.HomotopyTypeTheory.HomotopyTypeTheory.StratifiedInterchange`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/HomotopyTypeTheory/HomotopyTypeTheory_StratifiedInterchange.lean by skeleton subtraction
import Mathlib

/-!
# Stratified Interchange Algebras

We introduce the **Stratified Interchange Algebra (SIA)**, a novel algebraic structure
that captures the essential algebraic content of iterated loop spaces in homotopy
type theory. An SIA is a graded family of types, each equipped with two binary
operations (vertical and horizontal composition) sharing a common identity, connected
by the interchange law at every level.

The main innovation is packaging the entire tower of path-space operations into a
single algebraic structure and deriving commutativity at every level from the
interchange law via the Eckmann-Hilton argument — rather than axiomatizing it.

## Main definitions

* `HoTT.StratifiedInterchangeAlgebra` — The novel graded algebraic structure
* `HoTT.StratifiedInterchangeAlgebra.iterateComp` — Iterated composition (power map)

## Main results

* `vcomp_eq_hcomp` — Vertical and horizontal composition coincide (from EH)
* `vcomp_comm` — Composition is commutative at every level (from EH)
* `vcomp_vinv` — Right inverse derived from left inverse + commutativity
* `vinv_vinv` — Double inverse is identity
* `vinv_vcomp_distrib` — Inverse distributes over composition (abelian case)
* `instCommGroupCarrier` — Each level is a commutative group (Mathlib cross-connection)
* `iterateComp_hom` — The power map is a group homomorphism (consequence of commutativity)

## Novel aspects

The SIA structure is, to our knowledge, the first formalization of a graded
interchange algebra as a self-contained algebraic object. It provides:

1. A purely algebraic axiomatization of the homotopy-theoretic phenomenon that
   π_n is abelian for n ≥ 2, without reference to topological spaces.
2. A clean separation between the groupoid structure (axioms) and
   commutativity (theorem, not axiom).
3. A foundation for formalizing stable homotopy theory algebraically.
-/

universe u

namespace HoTT

/-- A **Stratified Interchange Algebra (SIA)** is a novel algebraic structure consisting
    of a graded family of types `Carrier n`, each equipped with:
    - Two binary operations `vcomp` and `hcomp` (vertical and horizontal composition)
    - A common identity element `id`
    - An inverse operation `vinv`
    satisfying groupoid axioms for vertical composition and the interchange law
    relating vertical and horizontal composition.

    The key feature: commutativity is DERIVED (via the Eckmann-Hilton argument),
    not axiomatized. This makes SIA a minimal axiomatization of the algebraic
    structure of iterated loop spaces. -/
structure StratifiedInterchangeAlgebra where
  /-- The carrier type at each level n. Level n represents n-dimensional cells. -/
  Carrier : ℕ → Type u
  /-- Vertical composition at level n -/
  vcomp : (n : ℕ) → Carrier n → Carrier n → Carrier n
  /-- Horizontal composition at level n -/
  hcomp : (n : ℕ) → Carrier n → Carrier n → Carrier n
  /-- The identity element at level n -/
  id : (n : ℕ) → Carrier n
  /-- Vertical inverse at level n -/
  vinv : (n : ℕ) → Carrier n → Carrier n
  /-- Vertical composition is associative -/
  vcomp_assoc : ∀ n a b c, vcomp n (vcomp n a b) c = vcomp n a (vcomp n b c)
  /-- Identity is a left unit for vertical composition -/
  id_vcomp : ∀ n a, vcomp n (id n) a = a
  /-- Identity is a right unit for vertical composition -/
  vcomp_id : ∀ n a, vcomp n a (id n) = a
  /-- Vertical inverse is a left inverse -/
  vinv_vcomp : ∀ n a, vcomp n (vinv n a) a = id n
  /-- Identity is a left unit for horizontal composition -/
  id_hcomp : ∀ n a, hcomp n (id n) a = a
  /-- Identity is a right unit for horizontal composition -/
  hcomp_id : ∀ n a, hcomp n a (id n) = a
  /-- The interchange law: horizontal distributes over vertical -/
  interchange : ∀ n a b c d,
    hcomp n (vcomp n a b) (vcomp n c d) = vcomp n (hcomp n a c) (hcomp n b d)

namespace StratifiedInterchangeAlgebra

variable (A : StratifiedInterchangeAlgebra)

/-! ### Core structural theorems derived from interchange -/

-- !-- Proof: Instantiate interchange with (a, id, id, b).
-- LHS: hcomp (vcomp a (id)) (vcomp (id) b) = hcomp a b (by identity laws).
-- RHS: vcomp (hcomp a (id)) (hcomp (id) b) = vcomp a b (by identity laws).
-- Hence hcomp a b = vcomp a b. -- !--

/-- **Theorem 1 (Vertical = Horizontal)**: The vertical and horizontal compositions
    in any SIA are pointwise equal. This is the first half of the Eckmann-Hilton
    argument applied to the stratified setting. -/
theorem vcomp_eq_hcomp (n : ℕ) (a b : A.Carrier n) :
    A.vcomp n a b = A.hcomp n a b := by
  have key := A.interchange n a (A.id n) (A.id n) b
  rw [A.vcomp_id, A.id_vcomp, A.hcomp_id, A.id_hcomp] at key
  exact key.symm

-- !-- Proof: Instantiate interchange with (id, a, b, id).
-- LHS: hcomp (vcomp (id) a) (vcomp b (id)) = hcomp a b (by identity laws).
-- RHS: vcomp (hcomp (id) b) (hcomp a (id)) = vcomp b a (by identity laws).
-- So hcomp a b = vcomp b a. Combined with vcomp_eq_hcomp: vcomp a b = vcomp b a. -- !--

/-- **Theorem 2 (Commutativity)**: Vertical composition in any SIA is commutative
    at every level. This is the full Eckmann-Hilton conclusion: the interchange law
    forces commutativity. In homotopy theory, this explains why π_n(X) is abelian
    for n ≥ 2: at those levels, both vertical and horizontal composition exist. -/
theorem vcomp_comm (n : ℕ) (a b : A.Carrier n) :
    A.vcomp n a b = A.vcomp n b a := by
  have key := A.interchange n (A.id n) a b (A.id n)
  rw [A.id_vcomp, A.vcomp_id, A.id_hcomp, A.hcomp_id] at key
  -- key : A.hcomp n a b = A.vcomp n b a
  rw [← A.vcomp_eq_hcomp] at key
  exact key


/-
!-- Proof of double inverse: vinv(vinv a) is the unique element x such that
vcomp (vinv a) x = id. Since vcomp (vinv a) a = id (axiom), we have
vinv(vinv a) = a by uniqueness of group inverse. -- !--

**Theorem 3 (Involution of inverse)**: The inverse operation is an involution.
    This is a standard group theory fact, but here derived purely from the SIA axioms
    without assuming a full group structure.
-/

/-
!-- In an abelian group, (ab)⁻¹ = a⁻¹b⁻¹. The proof uses:
(ab)(a⁻¹b⁻¹) = a(ba⁻¹)b⁻¹ = a(a⁻¹b)b⁻¹ = bb⁻¹ = e (using commutativity).
By uniqueness of inverse, (ab)⁻¹ = a⁻¹b⁻¹. -- !--

**Theorem 4 (Inverse distributes over composition)**: In an SIA, the inverse
    of a composition is the composition of inverses (in the same order, since
    composition is commutative). This is stronger than the general group theory
    result `(ab)⁻¹ = b⁻¹a⁻¹` because commutativity eliminates the reversal.
-/

/-! ### Cross-connection: Each level of an SIA is a commutative group -/

/-- Each level of a Stratified Interchange Algebra carries the structure of a
    commutative group. This establishes the connection between SIAs and Mathlib's
    algebraic hierarchy: an SIA is precisely a graded commutative group with
    additional horizontal structure satisfying interchange.

    This is a **cross-connection** to the Mathlib `CommGroup` typeclass, showing
    that SIA theory is compatible with and extends standard abstract algebra. -/
noncomputable instance instCommGroupCarrier (n : ℕ) : CommGroup (A.Carrier n) where
  mul := A.vcomp n
  one := A.id n
  inv := A.vinv n
  mul_assoc := A.vcomp_assoc n
  one_mul := A.id_vcomp n
  mul_one := A.vcomp_id n
  inv_mul_cancel := A.vinv_vcomp n
  mul_comm := A.vcomp_comm n

/-! ### Iterated composition and the power map homomorphism -/

/-- Iterated composition (power map) at level n. This defines `a^k` in the
    group at level n using the SIA's vertical composition. -/
def iterateComp (n : ℕ) (a : A.Carrier n) : ℕ → A.Carrier n
  | 0 => A.id n
  | k + 1 => A.vcomp n a (iterateComp n a k)

/-
!-- The power map is a homomorphism in any abelian group: (ab)^k = a^k · b^k.
Proof by induction on k. Base case: (ab)^0 = id = id · id = a^0 · b^0.
Inductive step: (ab)^{k+1} = ab · (ab)^k = ab · a^k · b^k
= a · a^k · b · b^k (by commutativity and associativity) = a^{k+1} · b^{k+1}. -- !--

**Theorem 5 (Power map homomorphism)**: The power map `a ↦ a^k` is a group
    homomorphism at every level of an SIA. This is a consequence of commutativity
    (Theorem 2) and is false for non-abelian groups, demonstrating that the SIA's
    commutativity has concrete algebraic consequences.

    **PEGB — Boundary**: This theorem is false for non-abelian groups. For example,
    in the symmetric group S₃, taking σ = (1 2) and τ = (1 3), we have
    (στ)² ≠ σ²τ² because στ = (1 3 2) has order 3, so (στ)² = (1 2 3),
    while σ² = τ² = id, so σ²τ² = id.
-/

/-! ### PEGB: Example — Trivial SIA -/

/-- The trivial SIA where every level is the unit type. This is the simplest
    non-degenerate example and corresponds to the contractible space in HoTT.

    **PEGB — Example**: Witnesses that the SIA axioms are consistent and
    non-vacuous. Every operation is the unique function on `Unit`. -/
def trivialSIA : StratifiedInterchangeAlgebra where
  Carrier := fun _ => Unit
  vcomp := fun _ _ _ => ()
  hcomp := fun _ _ _ => ()
  id := fun _ => ()
  vinv := fun _ _ => ()
  vcomp_assoc := fun _ _ _ _ => rfl
  id_vcomp := fun _ _ => rfl
  vcomp_id := fun _ _ => rfl
  vinv_vcomp := fun _ _ => rfl
  id_hcomp := fun _ _ => rfl
  hcomp_id := fun _ _ => rfl
  interchange := fun _ _ _ _ _ => rfl

/-
In the trivial SIA, iteration always yields the identity.
-/

/-! ### PEGB: Generalization — SIA with suspension maps -/

/-- A **Suspended SIA** extends the basic SIA with suspension homomorphisms
    connecting adjacent levels. This captures the full structure of homotopy groups
    with their suspension maps Σ : π_n(X) → π_{n+1}(ΣX).

    **PEGB — Generalization**: The basic SIA captures single-level structure;
    the suspended SIA captures inter-level relationships. The Freudenthal
    suspension theorem would constrain when `susp` is an isomorphism. -/
structure SuspendedSIA extends StratifiedInterchangeAlgebra where
  /-- Suspension map from level n to level n+1 -/
  susp : (n : ℕ) → Carrier n → Carrier (n + 1)
  /-- Suspension preserves identity -/
  susp_id : ∀ n, susp n (id n) = id (n + 1)
  /-- Suspension is a homomorphism with respect to vertical composition -/
  susp_vcomp : ∀ n a b, susp n (vcomp n a b) = vcomp (n + 1) (susp n a) (susp n b)

namespace SuspendedSIA

variable (S : SuspendedSIA)

/-
!-- susp preserves inverses: susp(a⁻¹) · susp(a) = susp(a⁻¹ · a) = susp(id) = id.
By uniqueness of inverse, susp(a⁻¹) = susp(a)⁻¹. -- !--

Suspension preserves inverses. This follows from the fact that suspension
    is a group homomorphism and group homomorphisms preserve inverses.
-/

/-- The kernel of the suspension map at level n consists of elements mapped to
    the identity at level n+1. This is a subgroup by standard algebra. -/
def suspKernel (n : ℕ) : Set (S.Carrier n) :=
  {a | S.susp n a = S.id (n + 1)}


/-
!-- If a, b are in the kernel, then susp(ab) = susp(a) · susp(b) = id · id = id,
so ab is in the kernel. -- !--

The kernel of suspension is closed under composition.
-/

end SuspendedSIA

/-! ### PEGB: Boundary — Non-abelian groups show interchange is essential -/

/-
!-- The symmetric group S₃ ≅ Equiv.Perm (Fin 3) is non-abelian.
This shows that without the interchange axiom (which forces commutativity),
a groupoid at a given level need not be commutative. The interchange law
is the essential ingredient that makes SIA levels commutative. -- !--

**Boundary**: There exist non-commutative groups, showing that the interchange
    law in the SIA definition is essential for deriving commutativity. Without it,
    a groupoid structure alone does not force the operation to be commutative.

    This witnesses `Equiv.Perm (Fin 3)` ≅ S₃ as a concrete non-abelian group.
-/

end StratifiedInterchangeAlgebra

end HoTT


