-- Prove2me | Theorems.Thm_mme_dwz_fixed_square_child_word_restrict_prescribed_parent
-- name    : mme_dwz_fixed_square_child_word_restrict_prescribed_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-18T15:01:16.655097+00:00
-- url     : https://prove2.me/theorems/56479d41-b83e-4f0a-ab43-121534230236
-- title:
--   A prescribed fourth-power parent restricts to every profile-compatible square-child word
-- statement:
--   Let $K$ be a field and let $q\ge0$. Write $S_{a,b,c}$ for the literal $(a,b,c)$ graded constituent of $\mathrm{CW}_q^{\otimes2}$, and $T_{I,J,L}$ for the literal fourth-power constituent. Let $p$ be an integer Z-split profile with positive denominator $D$ and counts $p_a$ summing to $D$. For $m\ge0$, set $n=Dm$.
--
--   At every position $r\in\{0,\ldots,n-1\}$ choose ordered child grade triples $s_r,t_r\in\{0,\ldots,4\}^3$ such that
--   $$
--   s_r+t_r=(I,J,L).
--   $$
--   Suppose the left child's Z grades have exactly the prescribed histogram:
--   $$
--   \#\{r:(s_r)_Z=a\}=m p_a\qquad(a=0,\ldots,4).
--   $$
--   Then there is a mode-wise linear tensor restriction
--   $$
--   T_{I,J,L}^{\otimes n}[p]
--   \longrightarrow
--   \bigotimes_{r=0}^{n-1}\bigl(S_{s_r}\otimes S_{t_r}\bigr).
--   $$
--   Here the source is the actual canonical Z-coordinate projection retaining precisely the words whose left-square grade histogram is $mp$. The target is the ordered product of the actual canonical square constituents. No tensor restriction or coefficient-preservation premise is assumed.
--
--   This applies directly to each regional prescribed $(1,1,6)$ parent. It also includes $m=0$, $q=0$, and zero child constituents; no nonzero-target conclusion is asserted. It supplies one fixed-address child product, not simultaneous extraction of many addresses, a positive-component value bound, or an exponent bound. Choosing address words with a specified joint type and establishing multiplicity are separate tasks.
-- source:
--   Derived canonical-coordinate restriction from Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5, Section 3.5 (leveled CW partitions), Section 3.9 (restricted-splitting tensor powers), and Section 7.1 (parent-to-child component partition). This is the finite fixed-address profile-preserving tensor bridge, not a separately numbered value theorem in the paper.

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME MME.TensorObj MME.StothersFourth MME.CompleteSplit.CWFourth
  MME.DWZRestrictedValue
open scoped Classical
universe u
set_option autoImplicit false

theorem mme_dwz_fixed_square_child_word_restrict_prescribed_parent {K : Type u} [Field K] (q : ℕ)
    (I J L : Fin 9) (p : IntegerZSplitProfile 5) (m : ℕ)
    (sx sy : Fin (p.length m) → Fin 3 → Fin 5)
    (hsum : ∀ r i, (sx r i).val + (sy r i).val = (cwFourthBlockType I J L i).val)
    (hprofile : ∀ a : Fin 5,
      (Finset.univ.filter (fun r : Fin (p.length m) ↦ sx r 2 = a)).card = p.count a*m) :
    TensorObj.Restrict
      (kronFin (p.length m) (fun r ↦
        kron ((cwSquareCanonicalGrading K q).blockSubtensor (sx r))
          ((cwSquareCanonicalGrading K q).blockSubtensor (sy r))))
      (prescribedZPower (cwFourthConstituent K q I J L)
        (constituentBasis K q I J L 2)
        (fun a : LiftedCoarseCoordinate.{u} q L ↦ cwSquarePairGrade q a.down.val.1)
        p m) := by sorry
