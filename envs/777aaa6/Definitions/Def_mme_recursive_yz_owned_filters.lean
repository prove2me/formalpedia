-- Prove2me | Definitions.Def_mme_recursive_yz_owned_filters
-- name    : mme_recursive_yz_owned_filters
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-12T10:16:25.51859+00:00
-- url     : https://prove2.me/theorems/5b4645b3-f127-41a3-a712-4b8220988842
-- title:
--   Concrete recursive CW grade, profile, and ownership filters
-- statement:
--   A retained fine word at a recursive address must have the actual child grade at each physical position and the prescribed full fine-word histogram in every cell. A retained Y word is compatible with exactly its own chosen address; the analogous condition is imposed on Z words. X words retain their full cell profile. These are concrete coordinate filters on both recursive halves.
--
--   The boundary-profile conditions encode the identities forced by nonzero CW coefficients: if the Z grade is zero, Y's profile is the coordinatewise reversed X profile; if the X grade is zero, Z's profile is the reversed Y profile; if the Y grade is zero, Z's profile is the reversed X profile. These identities, together with the coordinate filters, are used to prove actual tensor extraction.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Remark 6.1 and Sections 6.3--6.4; https://arxiv.org/html/2404.16349v2. Exact finite full-word predicates for the recursive filtering step.

import Definitions.Def_mme_recursive_yz_physical_words

open BigOperators MME.CompleteSplit
set_option autoImplicit false
namespace MME.RecursiveYZ

/-- Actual child-word grades at both halves of a selected recursive address. -/
def Graded {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (i : Fin 3) (a : Address half R parent n) (f : Position n → CompleteWord ell) : Prop :=
  ∀ p, ∑ r, (f p r).val = ((fullCell htotal a p).2.val i).val

/-- The actual useful-copy filters, with unique Y and Z compatibility among the
chosen addresses. X is kept by its full fine-cell profile. -/
noncomputable def Owned {half R ell k : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (address : Fin k → Address half R parent n)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (j : Fin k) (i : Fin 3) (f : Position n → CompleteWord ell) : Prop :=
  Graded htotal i (address j) f ∧ Useful (fullCell htotal (address j)) (mu i) f ∧
    (i = 1 → ∀ j', Compatible (fullCell htotal (address j')) yBoundary
      (modeGroup 1) (mu 1) f → j' = j) ∧
    (i = 2 → ∀ j', Compatible (fullCell htotal (address j')) zBoundary
      (modeGroup 2) (mu 2) f → j' = j)

/-- The profile equalities forced by the three CW boundary cases. -/
def BoundaryProfiles {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ) : Prop :=
  (∀ c, (c.2.val 2).val = 0 → ∀ w, mu 1 c w = mu 0 c (fun r ↦ Fin.rev (w r))) ∧
  (∀ c, (c.2.val 0).val = 0 → ∀ w, mu 2 c w = mu 1 c (fun r ↦ Fin.rev (w r))) ∧
  (∀ c, (c.2.val 1).val = 0 → ∀ w, mu 2 c w = mu 0 c (fun r ↦ Fin.rev (w r)))

end MME.RecursiveYZ


