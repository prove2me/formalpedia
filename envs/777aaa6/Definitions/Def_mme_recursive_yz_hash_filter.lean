-- Prove2me | Definitions.Def_mme_recursive_yz_hash_filter
-- name    : mme_recursive_yz_hash_filter
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-12T10:31:51.732469+00:00
-- url     : https://prove2.me/theorems/95f06af4-e21c-4fb6-aaf5-3b9506f10d50
-- title:
--   Actual recursive Y/Z hole sets and usable copies
-- statement:
--   For each recursive address, an unbroken fine block is a full fine-word assignment with the actual child grade at every physical position and the prescribed exact cell histograms. Its full-parent counts record the ordered pair of child words, jointly within the fixed coarse-mode word.
--
--   A type filter may remove some unbroken blocks. A retained block becomes ambiguous if a distinct compatible target address with the same Y or Z coarse word survives the same physical affine hash. The total hole set is the union of type-filter holes and collisions among blocks passing the type filter.
--
--   At a fixed hash state, an address is usable at repair parameter $d$ when both its Y and Z hole sets satisfy $4d|H_i|\le |U_i|$. These definitions specify the literal finite sets counted by the simultaneous-loss theorem. They do not assert that the type-filter or modulus budgets hold.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 6.3--6.5, Claim 6.21 and the Hole Lemma application; https://arxiv.org/html/2404.16349v2.

import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_recursive_x_hash_families

open BigOperators MME.CompleteSplit
set_option autoImplicit false
namespace MME.RecursiveYZ

def yzMode (i : Fin 2) : Fin 3 := ⟨i.val + 1, by omega⟩

def yzBoundary {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (i : Fin 2) : Cell half R parent → Prop :=
  if i = 0 then yBoundary else zBoundary

noncomputable def parentCounts {half R : ℕ} {n : Fin R → ℕ} {W : Type*}
    (y : ∀ r, Fin (n r) → Fin (half + 1)) (f : Position n → W)
    (r : Fin R) (j : Fin (half + 1)) (w : Fin 2 → W) : ℕ :=
  count (y r) (parentWord f r) j w

noncomputable def unbrokenWords {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (i : Fin 3) (a : Address half R parent n)
    (mu : Cell half R parent → CompleteWord ell → ℕ) :
    Finset (Position n → CompleteWord ell) := by
  classical
  exact Finset.univ.filter (fun f ↦ Graded htotal i a f ∧ Useful (fullCell htotal a) mu f)

noncomputable def ambiguous {half R ell N p : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset (ZMod p))
    (state : (Fin (N + 2) → ZMod p) × ZMod p) (i : Fin 2)
    (mu : Cell half R parent → CompleteWord ell → ℕ)
    (a : Address half R parent n) (f : Position n → CompleteWord ell) : Prop :=
  ∃ b ∈ RecursiveXHash.target m,
    RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a ∧
      Compatible (fullCell htotal b) (yzBoundary i) (modeGroup (yzMode i)) mu f ∧
      b ≠ a ∧ b ∈ RecursiveXHash.hashed m e S state

noncomputable def typeHoles {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (i : Fin 3) (a : Address half R parent n)
    (mu : Cell half R parent → CompleteWord ell → ℕ)
    (keep : (Position n → CompleteWord ell) → Prop) : Finset (Position n → CompleteWord ell) := by
  classical
  exact (unbrokenWords htotal i a mu).filter (fun f ↦ ¬ keep f)

noncomputable def collisionHoles {half R ell N p : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset (ZMod p))
    (state : (Fin (N + 2) → ZMod p) × ZMod p) (i : Fin 2)
    (mu : Cell half R parent → CompleteWord ell → ℕ)
    (a : Address half R parent n) (keep : (Position n → CompleteWord ell) → Prop) :
    Finset (Position n → CompleteWord ell) := by
  classical
  exact (unbrokenWords htotal (yzMode i) a mu).filter
    (fun f ↦ keep f ∧ ambiguous htotal m e S state i mu a f)

noncomputable def filterHoles {half R ell N p : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset (ZMod p))
    (state : (Fin (N + 2) → ZMod p) × ZMod p) (i : Fin 2)
    (mu : Cell half R parent → CompleteWord ell → ℕ)
    (a : Address half R parent n) (keep : (Position n → CompleteWord ell) → Prop) :
    Finset (Position n → CompleteWord ell) :=
  typeHoles htotal (yzMode i) a mu keep ∪ collisionHoles htotal m e S state i mu a keep

noncomputable def usable {half R ell N p : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset (ZMod p))
    (state : (Fin (N + 2) → ZMod p) × ZMod p) (d : ℕ)
    (mu : Fin 2 → Cell half R parent → CompleteWord ell → ℕ)
    (keep : Fin 2 → Address half R parent n → (Position n → CompleteWord ell) → Prop) :
    Finset (Address half R parent n) := by
  classical
  exact (RecursiveXHash.target m).filter (fun a ↦ ∀ i,
    4 * d * (filterHoles htotal m e S state i (mu i) a (keep i a)).card ≤
      (unbrokenWords htotal (yzMode i) a (mu i)).card)

end MME.RecursiveYZ


