-- Prove2me | Definitions.Def_mme_complete_split_112_address_words
-- name    : mme_complete_split_112_address_words
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-06T21:42:56.730095+00:00
-- url     : https://prove2.me/theorems/12d83930-973a-41c0-bdc8-cf07e1927d90
-- title:
--   Complete 112 fine words and rational profile formula
-- statement:
--   For the coupled $(1,1,2)$ constituent of the CW square, record the full two-letter fine word associated with each internal grade. In the $X$ and $Y$ modes the two supported grades correspond to $01,10$; the unused third grade is assigned $00$. In the $Z$ mode the three grades correspond to $20,02,11$.
--
--   For a rational parameter $p$, record the raw mode distributions
--
--   $$\beta_X(01)=\beta_X(10)=\beta_Y(01)=\beta_Y(10)=\frac12,\qquad \beta_Z(02)=\beta_Z(20)=p,\quad\beta_Z(11)=1-2p,$$
--
--   with all other values zero. No range, normalization or tensor-value statement is hidden in these definitions. They connect the existing retained coupled-address types to the source's full complete profiles.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4–3.6 (printed pp14–15); OSF https://osf.io/mw5ak/ code_matrix_mult.zip version1, src/evaluation/TermInfoLv2.m lines134–146, defining the 112 complete profiles. Exact released specialization: data/W1.00_2.371339.mat params(923), SHA256783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3. Address marginals reuse the coupled four-block laser-method profile of Coppersmith–Winograd1990 journal p270, public CWQ6ExactCoupledAddress (its finite definition is independent of q). The fine-word translation agrees with public dwzCanonical112Pair: XY grades0,1 correspond to01,10; Z grades0,1,2 correspond to20,02,11. This is an exact finite histogram bridge, not a component-value assertion.

import Definitions.Def_mme_CW_q6_primary_hash_family
import Mathlib.Data.Rat.Cast.Defs

set_option autoImplicit false
set_option warningAsError true

namespace MME.CompleteSplit112

/-- Complete canonical fine word of an internal coupled grade.
The unused X/Y grade 2 is assigned 00; exact addresses have zero such entries. -/
def fineWord (mode grade : Fin 3) : Fin 2 → Fin 3 :=
  if mode.val = 2 then
    if grade.val = 0 then ![2, 0]
    else if grade.val = 1 then ![0, 2] else ![1, 1]
  else if grade.val = 0 then ![0, 1]
    else if grade.val = 1 then ![1, 0] else ![0, 0]

/-- Exact rational 112 complete-profile formula, without assuming that p is
in its probability range or that these data are normalized. -/
def profileProbability (p : ℚ) (mode : Fin 3) (word : Fin 2 → Fin 3) : ℚ :=
  if mode.val = 2 then
    if ((word 0).val = 0 ∧ (word 1).val = 2) ∨
        ((word 0).val = 2 ∧ (word 1).val = 0) then p
    else if (word 0).val = 1 ∧ (word 1).val = 1 then 1 - 2 * p else 0
  else if ((word 0).val = 0 ∧ (word 1).val = 1) ∨
      ((word 0).val = 1 ∧ (word 1).val = 0) then 1 / 2 else 0

end MME.CompleteSplit112


