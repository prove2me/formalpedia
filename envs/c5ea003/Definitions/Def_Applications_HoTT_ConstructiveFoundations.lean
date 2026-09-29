-- Prove2me | Definitions.Def_Applications_HoTT_ConstructiveFoundations
-- name    : Applications_HoTT_ConstructiveFoundations
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:47:06.561736+00:00
-- url     : https://prove2.me/theorems/02e257ee-4e80-493c-bd19-8dda1036694e
-- title:
--   Aether Catalog definitions — Applications_HoTT_ConstructiveFoundations
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.HoTT.ConstructiveFoundations`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/HoTT/ConstructiveFoundations.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Constructive Foundations from Homotopy Type Theory

A *self-contained* fragment of Homotopy Type Theory, developed inside Lean 4
**without** relying on Lean's `Eq` (which has definitional proof irrelevance and
therefore validates UIP, making genuine HoTT impossible).  Instead we introduce
a synthetic Martin-Löf identity type `Path`, valued in `Type`, eliminated only
by path induction (`Path.rec`).  Because `Path` is an *indexed inductive in
`Type`*, axiom K / UIP is **not** derivable for it, so it genuinely models the
homotopical identity type.

The load-bearing results of this file are:

* `equiv_iff_contr_fibers` — the coincidence of the two notions of equivalence:
  a map has a quasi-inverse iff all of its fibers are contractible.
* `fundamental_theorem_id` — the (full biconditional) Fundamental Theorem of
  Identity Types: a fibrewise family `f : ∀ x, Path a x → C x` is a fibrewise
  equivalence iff the total space `Σ x, C x` is contractible.
* `equivalence_induction` — the equivalence-induction principle unlocked by a
  `Univalence` hypothesis: to prove a property of every equivalence out of `A`
  it suffices to prove it of the identity equivalence.
* `PTrunc` / `PTrunc.rec` / `PTrunc.rec_unique` — propositional truncation, a
  genuine higher inductive type (the `(-1)`-truncation) realized as a quotient,
  with its recursion principle and uniqueness.

The development is deliberately library-free (no `import Mathlib`): every result
is proved from the synthetic path calculus.
-/

namespace ConstructiveFoundations

universe u v w v2 z vv

/-! ## The synthetic identity type and its groupoid structure -/

/-- Synthetic Martin-Löf identity type, valued in `Type` (not `Prop`), so that
Lean's definitional proof irrelevance does not collapse it.  Path induction is
the recursor `Path.rec`; UIP is **not** provable. -/
inductive Path {A : Type u} : A → A → Type u where
  | refl (a : A) : Path a a


/-- Path concatenation (composition in the groupoid). -/
def Path.trans {A : Type u} {a b c : A} : Path a b → Path b c → Path a c
  | .refl _, q => q



-- !-- Lab Notebook: groupoid laws -- !--
-- !-- Hypothesis: refl/symm/trans/ap/transport satisfy the ∞-groupoid laws up to Path. -- !--
-- !-- Result: All proved by a single `cases` (path induction) collapsing to refl. -- !--
-- !-- Insight: Because `Path` is Type-valued, `cases p` IS the J-eliminator; it never -- !--
-- !--          uses K, so these are honest homotopical identities, not UIP artifacts. -- !--
-- !-- End Lab Notebook -- !--












/-! ## Contractibility, fibers, and the two notions of equivalence -/








/-! ### Based path spaces are contractible -/


-- !-- Lab Notebook: singleton_contr -- !--
-- !-- Hypothesis: The based path space Σ x, (a = x) is contractible. -- !--
-- !-- Result: Proved by path induction on the second component. -- !--
-- !-- Insight: This is THE workhorse: contractibility of singletons is what powers -- !--
-- !--          equivalence induction and the fundamental theorem of identity types. -- !--
-- !-- End Lab Notebook -- !--


/-! ### Closure of contractibility and total maps -/


-- !-- Lab Notebook: totalMap_qinv / isContr_of_qinv -- !--
-- !-- Hypothesis: A fibrewise quasi-inverse lifts to a quasi-inverse of total maps; -- !--
-- !--             and quasi-inverses preserve contractibility. -- !--
-- !-- Result: Both proved by lifting homotopies through `ap (⟨X, ·⟩)` and trans. -- !--
-- !-- Insight: Only the EASY (fibrewise → total) direction is needed downstream; it -- !--          requires no coherence, just `ap` into the fixed-index slice. -- !--
-- !-- End Lab Notebook -- !--




/-! ## Theorem 1: the two notions of equivalence coincide -/

-- !-- Lab Notebook: equiv_iff_contr_fibers -- !--
-- !-- Hypothesis: QInv f ↔ IsEquiv f (quasi-inverse iff contractible fibers). -- !--
-- !-- Result: Easy direction (IsEquiv → QInv) is direct; hard direction goes through -- !--          half-adjoint adjointification (qinv_to_ishae) then ishae_to_isEquiv. -- !--
-- !-- Insight: Contractible fibers make "being an equivalence" a proposition; the -- !--          single coherence `tau` of IsHAE is exactly what an arbitrary QInv lacks. -- !--
-- !-- Failure analysis: A direct QInv → contractible-fiber path could not be closed -- !--          without the adjoint coherence; IsHAE is the necessary intermediary. -- !--
-- !-- End Lab Notebook -- !--


-- !-- Proof sketch (qinv_to_ishae): Adjointify by keeping g, eta and replacing the right -- !--
-- !-- homotopy with eps' b := (eps (f (g b)))⁻¹ ⬝ ap f (eta (g b)) ⬝ eps b; the triangle -- !--
-- !-- coherence tau is `adjoint_triangle`, proved from eta-naturality + cancellation (4.2.3). -- !--

-- !-- Proof sketch (ishae_to_isEquiv): Fiber center is ⟨g b, eps b⟩.  Path-induct on the -- !--
-- !-- fiber's path so b := f a; then `fib_eq (eta a) _` closes it, the triangle being -- !--
-- !-- exactly `trans_refl_right` composed with `symm tau` (HoTT 4.2.4). -- !--



/-! ### Total equivalence implies fibrewise equivalence (HoTT 4.7.7, one direction) -/

-- !-- Lab Notebook: fibrewise_of_total -- !--
-- !-- Hypothesis: If the total map `totalMap g` is an equivalence then each `g x` is. -- !--
-- !-- Result: Each fiber `Fib (g x) c` is a RETRACT of `Fib (totalMap g) ⟨x,c⟩`, and -- !--          retracts of contractible types are contractible. -- !--
-- !-- Insight: The retraction needs only ONE homotopy (ψ∘φ ~ id), which collapses to -- !--          `refl` after path-inducting on the fiber's path; the dependent Σ-path is -- !--          handled by `idxPath`/`valPath`/`transport_natural`. -- !--
-- !-- Failure analysis: A full fibrewise equivalence is unnecessary and would force the -- !--          harder φ∘ψ homotopy; the retract suffices because we only need contractibility. -- !--
-- !-- End Lab Notebook -- !--









/-! ## Theorem 2: the Fundamental Theorem of Identity Types -/

-- !-- Lab Notebook: fundamental_theorem_id -- !--
-- !-- Hypothesis: For f : ∀ x, Path a x → C x, (∀ x, IsEquiv (f x)) ↔ IsContr (Σ x, C x). -- !--
-- !-- Result: Forward direction is clean from singleton_contr + totalMap_qinv + -- !--          isContr_of_qinv. Backward direction manufactures the equivalences from a -- !--          single contractibility witness (encode-decode engine). -- !--
-- !-- Insight: The total space of f is Σ x, C x; over the contractible Σ x, Path a x it -- !--          is contractible iff f is a fibrewise equivalence. -- !--
-- !-- End Lab Notebook -- !--


-- !-- Proof sketch (ftid_backward) -- !--
-- totalMap f : Σ x, Path a x → Σ x, C x is a map between contractible spaces, hence a
-- quasi-inverse (qinv_between_contr).  Transferring fibrewise (total equivalence →
-- fibrewise equivalence, the converse of totalMap_qinv) gives each f x its inverse,
-- whence IsEquiv (f x) by isEquiv_of_qinv.
-- !-- End sketch -- !--


/-! ## Theorem 3: equivalence induction from univalence -/





-- !-- Lab Notebook: equivalence_induction -- !--
-- !-- Hypothesis: Univalence makes the space of equivalences out of A contractible, -- !--             yielding an induction principle based at the identity equivalence. -- !--
-- !-- Result: equivSpace_contr transfers singleton_contr_types across idToEquiv; then -- !--          transport along the contraction discharges the induction. -- !--
-- !-- Insight: The base case lands DEFINITIONALLY on the center ⟨A, idEquiv A⟩ because -- !--          idToEquiv refl = idEquiv A reduces, so `transport ... base` typechecks. -- !--
-- !-- End Lab Notebook -- !--




/-! ## Theorem 4: propositional truncation as a higher inductive type -/

-- !-- Lab Notebook: PTrunc -- !--
-- !-- Hypothesis: The (-1)-truncation ‖A‖ is the quotient of A by the total relation; -- !--             it is a mere proposition with the universal recursion principle. -- !--
-- !-- Result: PTrunc.is_prop (all elements equal), PTrunc.rec into any subsingleton, -- !--          PTrunc.rec_beta (computation) and PTrunc.rec_unique (uniqueness). -- !--
-- !-- Insight: Quot by `fun _ _ => True` IS propositional truncation; Quot.sound gives -- !--          the path constructor and Quot.lift the recursor, with the round-trip free. -- !--
-- !-- Failure analysis: Using synthetic `Path` here is unnecessary — a (-1)-type is an -- !--          h-prop, so Lean's `Eq` (which is proof-irrelevant) is exactly correct. -- !--
-- !-- End Lab Notebook -- !--

/-- Propositional truncation `‖A‖₋₁`, the `(-1)`-truncation, realized as the quotient
of `A` by the always-true relation. -/
def PTrunc (A : Type u) : Type u := Quot (fun (_ _ : A) => True)

/-- The point constructor `|a| : ‖A‖`. -/
def PTrunc.mk {A : Type u} (a : A) : PTrunc A := Quot.mk _ a


/-- The recursion principle: to map `‖A‖ → B` it suffices to give `A → B` with `B`
a mere proposition (a subsingleton). -/
def PTrunc.rec {A : Type u} {B : Type v} (hB : ∀ x y : B, x = y) (f : A → B) :
    PTrunc A → B :=
  Quot.lift f (fun a b _ => hB (f a) (f b))



end ConstructiveFoundations


