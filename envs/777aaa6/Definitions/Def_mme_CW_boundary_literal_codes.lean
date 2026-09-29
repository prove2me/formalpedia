-- Prove2me | Definitions.Def_mme_CW_boundary_literal_codes
-- name    : mme_CW_boundary_literal_codes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T23:01:05.678135+00:00
-- url     : https://prove2.me/theorems/0013b6a1-5869-4f92-802c-f0f9616918fe
-- title:
--   Grade-zero boundary words in the fourth CW power
-- statement:
--   A boundary letter is one of the `q+2` literal Coppersmith--Winograd summands whose first-mode coordinate is the zero basis vector: a middle term of weight one, the `(0,0,top)` term of weight zero, or the `(0,top,0)` term of weight two. A four-letter word records a literal summand of `CW_q^{⊗4}`; its total weight is exactly its grade in mode one, while mode zero has grade zero and mode two has the complementary grade.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Royal Soc. Edinburgh 143A (2013), Section 5 and Table 1, p. 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_CW_fourth_literal_support_words

open MME BigOperators

namespace MME.StothersFourth

set_option autoImplicit false

/-- A literal CW summand whose coordinate in mode zero is the zero basis coordinate. -/
abbrev CWBoundaryLetter (q : ℕ) := Fin q ⊕ Fin 2

/-- Embed a boundary letter in the public literal enumeration of the CW tensor. -/
def cwBoundaryLiteral (q : ℕ) : CWBoundaryLetter q → CWLiteralTerm q
  | Sum.inl i => Sum.inl (i, 0)
  | Sum.inr ⟨0, _⟩ => Sum.inr 0
  | Sum.inr ⟨1, _⟩ => Sum.inr 1

/-- The grade seen in mode one by a boundary letter. -/
def cwBoundaryWeight {q : ℕ} : CWBoundaryLetter q → ℕ
  | Sum.inl _ => 1
  | Sum.inr ⟨0, _⟩ => 0
  | Sum.inr ⟨1, _⟩ => 2

/-- Total mode-one grade of a four-letter boundary word. -/
def cwBoundaryWordWeight {q : ℕ} (w : Fin 4 → CWBoundaryLetter q) : ℕ :=
  ∑ r, cwBoundaryWeight (w r)

/-- Convert a boundary word to the four literal terms used by the fixed parenthesization of `CW_q^⊗4`. -/
def cwBoundaryWordLiteral {q : ℕ}
    (w : Fin 4 → CWBoundaryLetter q) (r : Fin 4) : CWLiteralTerm q :=
  cwBoundaryLiteral q (w r)

/-- Canonical fourth-power basis address of a boundary word in one tensor mode. -/
def cwBoundaryWordIndex {q : ℕ}
    (w : Fin 4 → CWBoundaryLetter q) (s : Fin 3) :=
  cwFourthIndexOfLiteralTerms q
    (cwBoundaryWordLiteral w 0) (cwBoundaryWordLiteral w 1)
    (cwBoundaryWordLiteral w 2) (cwBoundaryWordLiteral w 3) s

end MME.StothersFourth


